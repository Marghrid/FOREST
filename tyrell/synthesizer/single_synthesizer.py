import datetime
import time
from abc import ABC

from ..decider import Decider, ValidationDecider, Example
from ..distinguisher import Distinguisher
from ..enumerator import Enumerator, KTreeEnumerator
from ..interpreter import Interpreter, ValidationPrinter, NodeCounter, ValidationInterpreter
from ..logger import get_logger
from ..utils import nice_time

logger = get_logger('tyrell.synthesizer')


class SingleSynthesizer(ABC):

    def __init__(self, valid_examples, invalid_examples, dsl):
        self.max_depth = 6
        self.examples = [Example(x, True) for x in valid_examples] + [Example(x, False) for x in invalid_examples]
        self.dsl = dsl
        self._printer = ValidationPrinter()
        self._distinguisher = Distinguisher()
        self._decider = ValidationDecider(interpreter=ValidationInterpreter(), examples=self.examples)
        self._node_counter = NodeCounter()
        self.indistinguishable = 0

        self.num_attempts = 0
        self.num_interactions = 0
        self.program = None
        self.start_time = None

    @property
    def enumerator(self):
        return self._enumerator

    @property
    def decider(self):
        return self._decider

    def synthesize(self):
        logger.info("Using FunnyEnumerator.")
        self.start_time = time.time()

        for dep in range(3, self.max_depth + 1):
            logger.info(f'Synthesizing programs of depth {dep}...')
            self._enumerator = KTreeEnumerator(self.dsl, depth=dep)

            self.program = self.try_for_depth()

            if self.program is not None:
                logger.info(f'Synthesizer done.\n'
                            f'  Enumerator: {self._enumerator.__class__.__name__}\n'
                            f'  Enumerated: {self.num_attempts}\n'
                            f'  Interactions: {self.num_interactions}\n'
                            f'  Elapsed time: {round(time.time() - self.start_time, 2)}\n'
                            f'  Solution: {self._printer.eval(self.program, ["IN"])}\n'
                            f'  Nodes: {self._node_counter.eval(self.program, [0])}')
                return self.program

    def enumerate(self):
        self.num_attempts += 1
        program = self._enumerator.next()
        if program is None: return
        if self._printer is not None:
            logger.debug(f'Enumerator generated: {self._printer.eval(program, ["IN"])}')
        else:
            logger.debug(f'Enumerator generated: {program}')

        if self.num_attempts > 0 and self.num_attempts % 1000 == 0:
            logger.info(
                f'Enumerated {self.num_attempts} programs in {nice_time(round(time.time() - self.start_time))}.')
            logger.info(f'DSL has {len(self._enumerator.dsl.predicates())} predicates.')

        return program

    def try_for_depth(self):
        program = self.enumerate()
        while program is not None:
            new_predicates = None

            res = self._decider.analyze(program)

            if res.is_ok():  # program satisfies I/O examples
                logger.info(
                    f'Program accepted. {self._node_counter.eval(program, [0])} nodes. {self.num_attempts} attempts '
                    f'and {round(time.time() - self.start_time, 2)} seconds:')
                logger.info(self._printer.eval(program, ["IN"]))
                return program

            else:
                new_predicates = res.why()
                if new_predicates is not None:
                    for pred in new_predicates:
                        pred_str = self._printer.eval(pred.args[0], ["IN"])
                        logger.debug(f'New predicate: {pred.name} {pred_str}')

            self._enumerator.update(new_predicates)
            # self._enumerator.update(None)
            program = self.enumerate()
