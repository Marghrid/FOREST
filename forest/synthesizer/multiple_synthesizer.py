import re
import time
from abc import ABC, abstractmethod

from termcolor import colored

from forest.spec import TyrellSpec
from ..capturer import Capturer
from ..decider import RegexDecider, Example
from ..distinguisher import RegexDistinguisher
from ..logger import get_logger
from ..utils import nice_time, is_regex, yes_values, no_values, conditions_to_str
from ..visitor import RegexInterpreter, NodeCounter

logger = get_logger('forest')


class MultipleSynthesizer(ABC):
    """ Interactive synthesizer. Finds more than one program consistent with the
    examples. """

    def __init__(self, valid_examples, invalid_examples, captured, condition_invalid,
                 dsl: TyrellSpec, ground_truth: str, pruning=True,
                 auto_interaction=False):


        self.valid = valid_examples
        self.invalid = invalid_examples
        self.captured = captured
        self.condition_invalid = condition_invalid
        self.dsl = dsl
        self.pruning = pruning
        self.ground_truth = ground_truth
        self.auto_interaction = auto_interaction

        if not pruning:
            logger.warning('Synthesizing without pruning the search space.')
        # If auto-interaction is enabled, the ground truth must be a valid regex.
        if self.auto_interaction:
            assert len(self.ground_truth) > 0 and is_regex(self.ground_truth)

        # Initialize components
        self._printer = RegexInterpreter()  # Works like to_string
        self._distinguisher = RegexDistinguisher()
        self._decider = RegexDecider(interpreter=RegexInterpreter(),
                                     valid_examples=self.valid+self.condition_invalid,
                                     invalid_examples=self.invalid)

        # Capturer works like a synthesizer of capturing groups
        self._capturer = Capturer(self.valid, self.captured, self.condition_invalid)
        self._node_counter = NodeCounter()

        # Subclass decides which enumerator to use
        self._enumerator = None

        # To store synthesized regexes and captures:
        self.regexes = []
        self.capture_conditions = None

        # counters and timers:
        self.indistinguishable = 0
        # Number of indistinguishable programs after which the synthesizer returns.
        self.max_indistinguishable = 3
        self.num_enumerated = 0
        self.num_interactions = 0
        self.start_time = None
        self.regex_synthesis_time = 0
        self.capture_synthesis_time = 0
        self.distinguish_time = 0
        self.last_print_time = time.time()
        self.per_depth_times = {}

        # Used in signal handling:
        self.die = False

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
        logger.info(f'Synthesizer done.\n'
                    f'  Enumerator: {self._enumerator}'
                    f'{" (no pruning)" if not self.pruning else ""}\n'
                    f'  Enumerated: {self.num_enumerated}\n'
                    f'  Interactions: {self.num_interactions}\n'
                    f'  Elapsed time: {round(time.time() - self.start_time, 2)}\n'
                    f'  Regex time: {round(self.regex_synthesis_time, 2)}\n'
                    f'  Distinguish time: {round(self.distinguish_time, 2)}\n'
                    f'  Capture time: {round(self.capture_synthesis_time, 2)}\n'
                    f'  Time per depth: {self.per_depth_times}')
        if len(self.regexes) > 0:
            regex, captures = self.regexes[0]
            conditions, conditions_captures = self.capture_conditions
            solution_str = self._decider.interpreter.eval(regex, captures=conditions_captures)
            if len(conditions) > 0:
                solution_str += ', ' + conditions_to_str(conditions)
            logger.info(f'  Solution: {solution_str}\n'
                        f'  Nodes: {self._node_counter.eval(*self.regexes[0])}\n')
            if len(captures) > 0:
                logger.info(f'  Captures: {self._decider.interpreter.eval(regex, captures=captures)}\n'
                            f'  Cap. groups: {len(captures)}')
            else:
                logger.info("  No capturing groups.")
        else:
            logger.info(f'  No solution.')

        if self.ground_truth is not None:
            logger.info(f'  Ground truth: {self.ground_truth}')

    def distinguish(self):
        """ Generate a distinguishing input between programs (if there is one),
        and interact with the user to disambiguate. """
        start_distinguish = time.time()
        dist_input, keep_if_valid, keep_if_invalid, unknown = \
            self._distinguisher.distinguish(self.regexes)
        if dist_input is not None:
            interaction_start_time = time.time()
            self.num_interactions += 1
            logger.info(
                f'Distinguishing input "{dist_input}" in '
                f'{round(time.time() - start_distinguish, 2)} seconds')
            for regex in unknown:
                r0 = self._decider.interpreter.eval(regex)
                if re.fullmatch(r0, dist_input):
                    keep_if_valid.append(regex)
                else:
                    keep_if_invalid.append(regex)
            if not self.auto_interaction:
                self.interact(dist_input, keep_if_valid, keep_if_invalid)
            else:
                self.auto_distinguish(dist_input, keep_if_valid, keep_if_invalid)
            self.start_time += time.time() - interaction_start_time

        else:  # programs are indistinguishable
            logger.info("Regexes are indistinguishable")
            self.indistinguishable += 1
            smallest_regex = min(self.regexes, key=lambda r: len(self._printer.eval(r)))
            self.regexes = [smallest_regex]

    def enumerate(self):
        """ Request new program from the enumerator. """
        self.num_enumerated += 1
        program = self._enumerator.next()
        if program is None:  # enumerator is exhausted
            return
        if self._printer is not None:
            logger.debug(f'Enumerator generated: {self._printer.eval(program)}')
        else:
            logger.debug(f'Enumerator generated: {program}')

        if self.num_enumerated > 0 and time.time() - self.last_print_time > 30:
            logger.info(
                f'Enumerated {self.num_enumerated} regexes in '
                f'{nice_time(time.time() - self.start_time)}.')
            self.last_print_time = time.time()

        return program

    def interact(self, dist_input, keep_if_valid, keep_if_invalid):
        """ Interact with user to ascertain whether the distinguishing input is valid """
        valid_answer = False
        # Do not count time spent waiting for user input: add waiting time to start_time.
        while not valid_answer:
            x = input(f'Is "{dist_input}" valid?\n')
            if x.lower().rstrip() in yes_values:
                logger.info(f'"{dist_input}" is {colored("valid", "green")}.')
                valid_answer = True
                self._decider.add_example([dist_input], True)
                self.regexes = keep_if_valid
                # self.indistinguishable = 0
            elif x.lower().rstrip() in no_values:
                logger.info(f'"{dist_input}" is {colored("invalid", "red")}.')
                valid_answer = True
                self._decider.add_example([dist_input], False)
                self.regexes = keep_if_invalid
                # self.indistinguishable = 0
            else:
                logger.info(f"Invalid answer {x}! Please answer 'yes' or 'no'.")

    def auto_distinguish(self, dist_input, keep_if_valid, keep_if_invalid):
        """ Simulate interaction """
        match = re.fullmatch(self.ground_truth, dist_input)
        if match is not None:
            logger.info(f'Auto: "{dist_input}" is {colored("valid", "green")}.')
            self._decider.add_example([dist_input], True)
            self.regexes = keep_if_valid
        else:
            logger.info(f'Auto: "{dist_input}" is {colored("invalid", "red")}.')
            self._decider.add_example([dist_input], False)
            self.regexes = keep_if_invalid

    def try_for_depth(self):
        while True:
            new_predicates = None

            regex_synthesis_start = time.time()
            regex = self.enumerate()

            if regex is None or self.die:  # enumerator is exhausted or user interrupted synthesizer
                break

            res = self._decider.analyze(regex)
            self.regex_synthesis_time += time.time() - regex_synthesis_start

            if res.is_ok():  # program satisfies I/O examples
                logger.debug(
                    f'Regex accepted. {self._node_counter.eval(regex, [0])} nodes. '
                    f'{self.num_enumerated} attempts '
                    f'and {round(time.time() - self.start_time, 2)} seconds:')
                logger.debug(self._printer.eval(regex))

                captures_synthesis_start = time.time()
                # synthesize captures that reflect the desired captured strings.
                captures = self._capturer.synthesize_capturing_groups(regex)
                self.capture_synthesis_time += time.time() - captures_synthesis_start

                if captures is None:
                    logger.info("Failed to find capture groups for the given captures.")
                    continue

                # Can I synthesize conditions that remove condition_invalid
                self.capture_conditions = self._capturer.synthesize_capture_conditions(regex)

                if self.capture_conditions[0] is None:
                    logger.info("Failed to find capture conditions that invalidate "
                                "condition_invalid.")
                    continue

                self.regexes.append((regex, captures))

                if len(self.regexes) >= 2:  # if there are more than 2 solutions, disambiguate.
                    distinguish_start = time.time()
                    self.distinguish()
                    self.distinguish_time += time.time() - distinguish_start

                assert len(self.regexes) == 1  # only one regex remains

                if self.indistinguishable >= self.max_indistinguishable:
                    break

            elif self.pruning:
                new_predicates = res.why()
                if new_predicates is not None:
                    for pred in new_predicates:
                        pred_str = self._printer.eval(pred.args[0])
                        if len(pred.args) > 1:
                            pred_str = str(pred.args[1]) + " " + pred_str
                        logger.debug(f'New predicate: {pred.name} {pred_str}')
                self._enumerator.update(new_predicates)
                continue
            self._enumerator.update(None)

        if len(self.regexes) > 0 or self.die:
            return
