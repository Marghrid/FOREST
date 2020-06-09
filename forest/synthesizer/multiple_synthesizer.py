import re
import time
from abc import ABC, abstractmethod

from termcolor import colored

from forest.spec import TyrellSpec
from ..decider import RegexDecider, Example
from ..distinguisher import Distinguisher
from ..logger import get_logger
from ..utils import nice_time, is_regex
from ..visitor import ValidationInterpreter, ValidationPrinter, NodeCounter

logger = get_logger('forest.synthesizer')

yes_values = {"yes", "valid", "true", "1", "+", "v", "y", "t"}
no_values = {"no", "invalid", "false", "0", "-", "i", "n", "f"}


class MultipleSynthesizer(ABC):
    """ Interactive synthesizer. Finds more than one program consistent with the
    examples. """

    def __init__(self, valid_examples, invalid_examples, dsl: TyrellSpec,
                 ground_truth: str,
                 pruning=True, auto_interaction=False):

        self.examples = [Example(x, True) for x in valid_examples] \
                        + [Example(x, False) for x in invalid_examples]
        self.dsl = dsl
        self.pruning = pruning
        if not pruning:
            logger.warning('Synthesizing without pruning the search space.')
        self.ground_truth = ground_truth
        self.auto_interaction = auto_interaction
        # If auto-interaction is enabled, the ground truth must be a valid regex.
        if self.auto_interaction:
            assert len(self.ground_truth) > 0 and is_regex(self.ground_truth)
        self._printer = ValidationPrinter()
        self._distinguisher = Distinguisher()
        self._decider = RegexDecider(interpreter=ValidationInterpreter(),
                                     examples=self.examples)

        self._node_counter = NodeCounter()

        # Subclass decides which enumerator to use
        self._enumerator = None

        self.indistinguishable = 0
        # Number of indistinguishable programs after which the synthesizer returns.
        self.max_indistinguishable = 3

        self.num_enumerated = 0
        self.num_interactions = 0
        self.programs = []
        self.start_time = None

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
        raise NotImplementedError

    def terminate(self):
        logger.info(f'Synthesizer done.\n'
                    f'  Enumerator: {self._enumerator}'
                    f'{" (no pruning)" if not self.pruning else ""}\n'
                    f'  Enumerated: {self.num_enumerated}\n'
                    f'  Interactions: {self.num_interactions}\n'
                    f'  Elapsed time: {round(time.time() - self.start_time, 2)}\n')
        if len(self.programs) > 0:
            logger.info(f'  Solution: {self._printer.eval(self.programs[0], ["IN"])}\n'
                        f'  Nodes: {self._node_counter.eval(self.programs[0], [0])}')
        else:
            logger.info(f'  No solution.')

        if self.ground_truth is not None:
            logger.info(f'  Ground truth: {self.ground_truth}')

    def distinguish(self):
        """ Generate a distinguishing input between programs (if there is one),
        and interact with the user to disambiguate. """
        start_distinguish = time.time()
        dist_input = self._distinguisher.distinguish(self.programs[0], self.programs[1])
        if dist_input is not None:
            interaction_start_time = time.time()
            self.num_interactions += 1
            logger.info(
                f'Distinguishing input "{dist_input}" in '
                f'{round(time.time() - start_distinguish, 2)} seconds')
            if not self.auto_interaction:
                self.interact(dist_input)
            else:
                self.auto_distinguish(dist_input)
            self.start_time += time.time() - interaction_start_time

        else:  # programs are indistinguishable
            logger.info("Programs are indistinguishable")
            self.indistinguishable += 1
            smallest_regex = min(self.programs,
                                 key=lambda r: len(self._printer.eval(r, ["IN"])))
            self.programs = [smallest_regex]

    def enumerate(self):
        """ Request new program from the enumerator. """
        self.num_enumerated += 1
        program = self._enumerator.next()
        if program is None: # enumerator is exhausted
            return
        if self._printer is not None:
            logger.debug(f'Enumerator generated: {self._printer.eval(program, ["IN"])}')
        else:
            logger.debug(f'Enumerator generated: {program}')

        if self.num_enumerated > 0 and self.num_enumerated % 1000 == 0:
            logger.info(
                f'Enumerated {self.num_enumerated} programs in'
                f'{nice_time(time.time() - self.start_time)}.')

        return program

    def interact(self, dist_input):
        """ Interact with user to ascertain whether the distinguishing input is valid """
        valid_answer = False
        # Do not count time spent waiting for user input: add waiting time to start_time.
        while not valid_answer:
            x = input(f'Is "{dist_input}" valid?\n')
            if x.lower().rstrip() in yes_values:
                logger.info(f'"{dist_input}" is {colored("valid", "green")}.')
                valid_answer = True
                self._decider.add_example([dist_input], True)
                r0 = self._decider.interpreter.eval(self.programs[0], [])
                if not re.fullmatch(r0, dist_input):
                    self.programs.pop(0)
                else:
                    self.programs.pop(1)
                    # self.indistinguishable = 0
            elif x.lower().rstrip() in no_values:
                logger.info(f'"{dist_input}" is {colored("invalid", "red")}.')
                valid_answer = True
                self._decider.add_example([dist_input], False)
                r0 = self._decider.interpreter.eval(self.programs[0], [])
                if not re.fullmatch(r0, dist_input):
                    self.programs.pop(1)
                else:
                    self.programs.pop(0)
                    # self.indistinguishable = 0
            else:
                logger.info(f"Invalid answer {x}! Please answer 'yes' or 'no'.")

    def auto_distinguish(self, dist_input):
        """ Simulate interaction """
        match = re.fullmatch(self.ground_truth, dist_input)
        if match is not None:
            logger.info(f'Auto: "{dist_input}" is {colored("valid", "green")}.')
            self._decider.add_example([dist_input], True)
            r0 = self._decider.interpreter.eval(self.programs[0], [])
            if not re.fullmatch(r0, dist_input):
                self.programs.pop(1)
            else:
                self.programs.pop(0)
        else:
            logger.info(f'Auto: "{dist_input}" is {colored("invalid", "red")}.')
            self._decider.add_example([dist_input], False)
            r0 = self._decider.interpreter.eval(self.programs[0], [])
            if not re.fullmatch(r0, dist_input):
                self.programs.pop(1)
            else:
                self.programs.pop(0)

    def try_for_depth(self):
        program = self.enumerate()
        while program is not None and not self.die:
            new_predicates = None

            res = self._decider.analyze(program)

            if res.is_ok():  # program satisfies I/O examples
                logger.info(
                    f'Program accepted. {self._node_counter.eval(program, [0])} nodes. {self.num_enumerated} attempts '
                    f'and {round(time.time() - self.start_time, 2)} seconds:')
                logger.info(self._printer.eval(program, ["IN"]))
                self.programs.append(program)
                if len(self.programs) >= 2:
                    self.distinguish()
                if self.indistinguishable >= self.max_indistinguishable:
                    break
            else:
                new_predicates = res.why()
                if new_predicates is not None:
                    for pred in new_predicates:
                        if pred.name.startswith("block_range"):
                            logger.debug(
                                f'New predicate: {pred.name} {pred.args[0]}')
                            continue
                        pred_str = self._printer.eval(pred.args[0], ["IN"])
                        if len(pred.args) > 1:
                            pred_str = str(pred.args[1]) + " " + pred_str
                        logger.debug(f'New predicate: {pred.name} {pred_str}')

            if self.pruning:
                self._enumerator.update(new_predicates)
            else:
                self._enumerator.update(None)
            program = self.enumerate()

        if len(self.programs) > 0 or self.die:
            self.terminate()
