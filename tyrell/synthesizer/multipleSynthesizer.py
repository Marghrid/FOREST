import datetime
import time
from abc import ABC

from ..decider import Decider
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

    @property
    def enumerator(self):
        return self._enumerator

    @property
    def decider(self):
        return self._decider

    def synthesize(self):
        '''
        A convenient method to enumerate ASTs until the result passes the analysis.
        Returns the synthesized program, or `None` if the synthesis failed.
        '''
        num_attempts = 0
        programs = []
        program = self._enumerator.next()
        while program is not None:
            num_attempts += 1
            new_predicates = None
            if self._printer is not None:
                logger.debug('Enumerator generated: ' + self._printer.eval(program, ["IN"]))
            else:
                logger.debug(f'Enumerator generated: {program}')

            if num_attempts % 500 == 0:
                currentDT = datetime.datetime.now()
                logger.info(f'Enumerated {num_attempts} programs at {currentDT.strftime("%H:%M:%S")}.')
            res = self._decider.analyze(program)
            if res.is_ok():
                logger.info(f'Program accepted after {num_attempts} attempts')
                programs.append(program)
                if len(programs) > 7:
                    return programs
            else:
                new_predicates = res.why()
                # logger.debug('Program rejected.')
                if new_predicates is not None:
                    for pred in new_predicates:
                        pred_str = self._printer.eval(pred.args[0], ["IN"])
                        logger.debug(f'New predicate: block {pred_str}')
            self._enumerator.update(new_predicates)
            program = self._enumerator.next()
        logger.info(
            'Enumerator is exhausted after {} attempts'.format(num_attempts))
        return programs
