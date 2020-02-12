from abc import ABC

from ..decider import Decider
from ..enumerator import Enumerator
from ..interpreter import InterpreterError
from ..logger import get_logger

logger = get_logger('tyrell.synthesizer')


class Synthesizer(ABC):
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
        program = self._enumerator.next()
        while program is not None:
            num_attempts += 1
            if self._printer is not None:
                logger.debug('Enumerator generated: ' + self._printer.eval(program, ["IN"]))
            else:
                logger.debug(f'Enumerator generated: {program}')
            try:
                res = self._decider.analyze(program)
                if res.is_ok():
                    logger.info(f'Program accepted after {num_attempts} attempts')
                    return program
                else:
                    new_predicates = res.why()
                    logger.debug('Program rejected.')
                    if new_predicates is not None:
                        logger.debug(f'New predicates: {new_predicates}')
                    self._enumerator.update(new_predicates)
                    program = self._enumerator.next()
            except InterpreterError as e:
                new_predicates = self._decider.analyze_interpreter_error(e)
                logger.debug('Interpreter {} failed. Exception: {}. Reason: {}'.format(self._decider.interpreter().__class__.__name__, e.__class__.__name__, new_predicates))
                self._enumerator.update(new_predicates)
                program = self._enumerator.next()
        logger.debug(
            'Enumerator is exhausted after {} attempts'.format(num_attempts))
        return None
