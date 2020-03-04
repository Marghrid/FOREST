import datetime
import time
from abc import ABC

from ..decider import Decider
from ..distinguisher import Distinguisher
from ..enumerator import Enumerator
from ..interpreter import InterpreterError
from ..logger import get_logger

logger = get_logger('tyrell.synthesizer')


class MultipleSynthesizer(ABC):
    _enumerator: Enumerator
    _decider: Decider

    def __init__(self, enumerator: Enumerator, decider: Decider, printer=None):
        self._enumerator = enumerator
        self._decider = decider
        self._printer = printer
        self._distinguisher = Distinguisher()

        self.num_attempts = 0
        self.programs = []

    @property
    def enumerator(self):
        return self._enumerator

    @property
    def decider(self):
        return self._decider

    def synthesize(self):
        self.start_time = time.time()
        program = self.enumerate()

        while program is not None:
            new_predicates = None

            res = self._decider.analyze(program)

            if res.is_ok():    # program satisfies I/O examples
                logger.info(f'Program accepted after {self.num_attempts} attempts and {round(time.time() - self.start_time)} seconds:')
                logger.info(self._printer.eval(program, ["IN"]))
                self.programs.append(program)
                if len(self.programs) > 1:
                    dist_input = self.distinguish(self.programs)
                    if dist_input is not None:
                        logger.info("Distinguishing input: " + dist_input)
                    else: # programs are indistinguishable
                        logger.info("Programs are indistinguishable")
                        # FIXME: Dirty hack!! I'm keeping the "shorter" program :)
                        p = min(self.programs, key=lambda p: len(self._printer.eval(p, ["IN"])))
                        self.programs = [p]
            else:
                new_predicates = res.why()
                if new_predicates is not None:
                    for pred in new_predicates:
                        pred_str = self._printer.eval(pred.args[0], ["IN"])
                        logger.debug(f'New predicate: block {pred_str}')

            self._enumerator.update(new_predicates)
            program = self.enumerate()
        logger.debug(f'Enumerator is exhausted after {self.num_attempts} attempts')
        if len(self.programs) > 0:
            return self.programs[0]
        else:
            return None

    def enumerate(self):
        self.num_attempts += 1
        program = self._enumerator.next()
        if program is None: return
        if self._printer is not None:
            logger.debug('Enumerator generated: ' + self._printer.eval(program, ["IN"]))
        else:
            logger.debug(f'Enumerator generated: {program}')

        if self.num_attempts > 0 and self.num_attempts % 500 == 0:
            current_dt = datetime.datetime.now()
            logger.info(f'Enumerated {self.num_attempts} programs in {round(time.time() - self.start_time)} seconds.')

        return program

    def distinguish(self, programs):
        return self._distinguisher.distinguish(programs[0], programs[1])
