import datetime
import re
import socket
import time
from abc import ABC, abstractmethod
from typing import List

from termcolor import colored

from forest.capturer import Capturer
from forest.configuration import Configuration
from forest.decider import RegexDecider
from forest.distinguisher import RegexDistinguisher
from forest.logger import get_logger
from forest.spec import TyrellSpec
from forest.stats import Statistics
from forest.utils import nice_time, is_regex, yes_values, no_values, conditions_to_str
from forest.visitor import RegexInterpreter, NodeCounter

logger = get_logger('forest')
stats = Statistics.get_statistics()


class MultipleSynthesizer(ABC):
    """ Interactive synthesizer. Finds more than one program consistent with the
    examples. """

    def __init__(self, valid_examples, invalid_examples, captured, condition_invalid,
                 dsl: TyrellSpec, ground_truth: str, configuration: Configuration):

        self.max_before_distinguishing = 2  # 2 for conversational clarification
        self.valid = valid_examples
        self.invalid = invalid_examples
        self.captured = captured
        self.condition_invalid = condition_invalid
        self.dsl = dsl
        self.configuration = configuration
        if ground_truth is None:
            self.ground_truth_conditions = None
            self.ground_truth_regex = None
        else:
            ground_truth = ground_truth.split(',')
            ground_truth_conditions = list(
                filter(lambda s: s.lstrip().startswith("$"), ground_truth))
            self.ground_truth_conditions = list(map(lambda s: s.lstrip(), ground_truth_conditions))
            self.ground_truth_regex = ",".join(
                filter(lambda s: not s.lstrip().startswith("$"), ground_truth))

        if not configuration.pruning:
            logger.warning('Synthesizing without pruning the search space.')
        # If auto-interaction is enabled, the ground truth must be a valid regex.
        if self.configuration.self_interact:
            assert len(self.ground_truth_regex) > 0 and is_regex(self.ground_truth_regex)

        # Initialize components
        self._printer = RegexInterpreter()  # Works like to_string
        self._distinguisher = RegexDistinguisher()
        self._decider = RegexDecider(interpreter=RegexInterpreter(),
                                     valid_examples=self.valid + self.condition_invalid,
                                     invalid_examples=self.invalid)

        # Capturer works like a synthesizer of capturing groups
        self._capturer = Capturer(self.valid, self.captured, self.condition_invalid,
                                  self.ground_truth_regex, self.ground_truth_conditions,
                                  self.configuration)
        self._node_counter = NodeCounter()

        # Subclass decides which enumerator to use
        self._enumerator = None

        # To store synthesized regexes and captures:
        self.solutions = []
        self.first_regex = None

        # counters and timers:
        self.indistinguishable = 0
        # Number of indistinguishable programs after which the synthesizer returns.
        self.max_indistinguishable = 3
        self.start_time = None
        self.last_print_time = time.time()

    @property
    def enumerator(self):
        return self._enumerator

    @property
    def decider(self):
        return self._decider

    @abstractmethod
    def synthesize(self):
        """ Main synthesis procedure. Implemented in subclasses. """
        raise NotImplementedError

    def terminate(self):
        stats.total_synthesis_time = round(time.time() - self.start_time, 2)
        logger.info(f'Synthesizer done.')

        now = datetime.datetime.now()
        info_str = f'On {socket.gethostname()} on {now.strftime("%Y-%m-%d %H:%M:%S")}.\n'
        info_str += f'Enumerator: {self._enumerator}' \
                    f'{" (no pruning)" if not self.configuration.pruning else ""}\n'
        info_str += f'Terminated: {self.configuration.die}\n'
        info_str += str(stats) + "\n\n"

        if len(self.solutions) > 0:
            if self.configuration.print_first_regex:
                first_regex_str = self._decider.interpreter.eval(self.first_regex)
                info_str += f'First regex: {first_regex_str}\n'
            regex, capturing_groups, capture_conditions = self.solutions[0]
            conditions, conditions_captures = capture_conditions
            solution_str = self._decider.interpreter.eval(regex, captures=conditions_captures)
            if len(conditions) > 0:
                solution_str += ', ' + conditions_to_str(conditions)
            info_str += f'Solution: {solution_str}\n' \
                        f'  Nodes: {self._node_counter.eval(self.solutions[0][0])}\n'
            if len(capturing_groups) > 0:
                info_str += f'  Cap. groups: ' \
                            f'{self._decider.interpreter.eval(regex, captures=capturing_groups)}\n' \
                            f'  Num. cap. groups: {len(capturing_groups)}'
            else:
                info_str += "  No capturing groups."
        else:
            info_str += f'  No solution.'

        info_str += '\n'

        if self.ground_truth_regex is not None:
            info_str += f'  Ground truth: {self.ground_truth_regex}' \
                        f' {", ".join(self.ground_truth_conditions)}'
        logger.info(info_str)

        if len(self.configuration.log_path) > 0:
            f = open(self.configuration.log_path, "w")
            f.write(info_str)

    def distinguish(self):
        """ Generate a distinguishing input between programs (if there is one),
        and interact with the user to disambiguate. """
        distinguish_start = time.time()
        dist_input, keep_if_valid, keep_if_invalid, unknown = \
            self._distinguisher.distinguish(self.solutions)
        if dist_input is not None:
            # interaction_start_time = time.time()
            stats.regex_interactions += 1
            logger.info(
                f'Distinguishing input "{dist_input}" in '
                f'{round(time.time() - distinguish_start, 2)} seconds')

            for regex in unknown:
                r0 = self._decider.interpreter.eval(regex)
                if re.fullmatch(r0, dist_input):
                    keep_if_valid.append(regex)
                else:
                    keep_if_invalid.append(regex)

            if not self.configuration.self_interact:
                self.interact(dist_input, keep_if_valid, keep_if_invalid)
            else:
                self.auto_distinguish(dist_input, keep_if_valid, keep_if_invalid)
            # self.start_time += time.time() - interaction_start_time

        else:  # programs are indistinguishable
            logger.info("Regexes are indistinguishable")
            self.indistinguishable += 1
            smallest_regex = min(self.solutions, key=lambda r: len(self._printer.eval(r)))
            self.solutions = [smallest_regex]
        stats.regex_distinguishing_time += time.time() - distinguish_start
        stats.regex_synthesis_time += time.time() - distinguish_start

    def enumerate(self):
        """ Request new program from the enumerator. """
        stats.enumerated_regexes += 1
        program = self._enumerator.next()
        if program is None:  # enumerator is exhausted
            return
        if self._printer is not None:
            logger.debug(f'Enumerator generated: {self._printer.eval(program)}')
        else:
            logger.debug(f'Enumerator generated: {program}')

        if stats.enumerated_regexes > 0 and time.time() - self.last_print_time > 30:
            logger.info(
                f'Enumerated {stats.enumerated_regexes} regexes in '
                f'{nice_time(time.time() - self.start_time)}.')
            self.last_print_time = time.time()

        return program

    def interact(self, dist_input, keep_if_valid, keep_if_invalid):
        """ Interact with user to ascertain whether the distinguishing input is valid """
        valid_answer = False
        # Do not count time spent waiting for user input: add waiting time to start_time.
        while not valid_answer and not self.configuration.die:
            x = input(f'Is "{dist_input}" valid? (y/n)\n')
            if x.lower().rstrip() in yes_values:
                logger.info(f'"{dist_input}" is {colored("valid", "green")}.')
                valid_answer = True
                self._decider.add_example([dist_input], True)
                self.solutions = keep_if_valid
                # self.indistinguishable = 0
            elif x.lower().rstrip() in no_values:
                logger.info(f'"{dist_input}" is {colored("invalid", "red")}.')
                valid_answer = True
                self._decider.add_example([dist_input], False)
                self.solutions = keep_if_invalid
                # self.indistinguishable = 0
            else:
                logger.info(f"Invalid answer {x}! Please answer 'yes' or 'no'.")

    def auto_distinguish(self, dist_input: str, keep_if_valid: List, keep_if_invalid: List):
        """ Simulate interaction """
        match = re.fullmatch(self.ground_truth_regex, dist_input)
        if match is not None:
            logger.info(f'Auto: "{dist_input}" is {colored("valid", "green")}.')
            self._decider.add_example([dist_input], True)
            self.solutions = keep_if_valid
        else:
            logger.info(f'Auto: "{dist_input}" is {colored("invalid", "red")}.')
            self._decider.add_example([dist_input], False)
            self.solutions = keep_if_invalid

    def try_for_depth(self):
        stats.first_regex_time = -1
        while True:
            regex = self.try_regex()

            if regex is None or self.configuration.die:  # enumerator is exhausted or user interrupted synthesizer
                break

            if regex == -1:  # enumerated a regex that is not correct
                continue

            if self.configuration.synth_captures:
                capturing_groups = self.try_capturing_groups(regex)

                if capturing_groups is None:
                    logger.info("Failed to find capture groups for the given captures.")
                    continue
            else:
                capturing_groups = []

            if self.configuration.synth_conditions:
                capture_conditions = self.try_capture_conditions(regex)

                if capture_conditions[0] is None:
                    logger.info("Failed to find capture conditions that invalidate condition_invalid.")
                    continue
            else:
                capture_conditions = []

            self.solutions.append((regex, capturing_groups, capture_conditions))

            if len(self.solutions) > 0 and not self.configuration.disambiguation:
                break

            if len(self.solutions) >= self.max_before_distinguishing:
                # if there are more than max_before_disambiguating solutions, disambiguate.
                self.distinguish()

            if self.indistinguishable >= self.max_indistinguishable:
                break
        while len(self.solutions) > 1:
            self.distinguish()
        assert len(self.solutions) <= 1  # only one regex remains

    def try_capture_conditions(self, regex):
        cap_conditions_synthesis_start = time.time()
        capture_conditions = self._capturer.synthesize_capture_conditions(regex)
        stats.cap_conditions_synthesis_time += time.time() - cap_conditions_synthesis_start
        return capture_conditions

    def try_capturing_groups(self, regex):
        cap_groups_synthesis_start = time.time()
        # synthesize captures that reflect the desired captured strings.
        captures = self._capturer.synthesize_capturing_groups(regex)
        stats.cap_groups_synthesis_time += time.time() - cap_groups_synthesis_start
        return captures

    def try_regex(self):
        regex_synthesis_start = time.time()

        regex = self.enumerate()
        if regex is None:
            return None

        analysis_result = self._decider.analyze(regex)

        if analysis_result.is_ok():  # program satisfies I/O examples
            logger.info(
                f'Regex accepted. {self._node_counter.eval(regex, [0])} nodes. '
                f'{stats.enumerated_regexes} attempts '
                f'and {round(time.time() - self.start_time, 2)} seconds:')
            logger.info(self._printer.eval(regex))
            self._enumerator.update()
            stats.regex_synthesis_time += time.time() - regex_synthesis_start
            if stats.first_regex_time == -1:
                stats.first_regex_time = time.time() - self.start_time
                self.first_regex = regex
            return regex

        elif self.configuration.pruning:
            new_predicates = analysis_result.why()
            if new_predicates is not None:
                for pred in new_predicates:
                    pred_str = self._printer.eval(pred.args[0])
                    if len(pred.args) > 1:
                        pred_str = str(pred.args[1]) + " " + pred_str
                    logger.debug(f'New predicate: {pred.name} {pred_str}')
        else:
            new_predicates = None
        self._enumerator.update(new_predicates)
        stats.regex_synthesis_time += time.time() - regex_synthesis_start
        return -1
