import datetime
import time
from abc import ABC

from ..decider import ExampleDecider
from ..distinguisher import Distinguisher
from ..enumerator import Enumerator, SmtEnumerator
from ..interpreter import Interpreter
from ..logger import get_logger

logger = get_logger('tyrell.synthesizer')

yes_values = {"yes","valid", "true", "1","+","v","y","t"}
no_values =  {"no","invalid","false","0","-","i","n","f"}


class MultipleSynthesizer(ABC):
    _enumerator: SmtEnumerator
    _decider: ExampleDecider
    _printer: Interpreter
    _distinguisher: Distinguisher

    def __init__(self, enumerator: SmtEnumerator, decider: ExampleDecider, printer=None):
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
                    self.distinguish()
            else:
                new_predicates = res.why()
                if new_predicates is not None:
                    for pred in new_predicates:
                        pred_str = self._printer.eval(pred.args[0], ["IN"])
                        logger.debug(f'New predicate: block {pred_str}')

            self._enumerator.update(new_predicates)
            program = self.enumerate()
        #logger.debug(f'Enumerator is exhausted after {self.num_attempts} attempts')
        logger.info(f'Synthesizer done for depth {self._enumerator.depth} after {self.num_attempts} attempts and {round(time.time() - self.start_time)} seconds')
        if len(self.programs) > 0:
            return self.programs[0]
        else:
            return None

    def distinguish(self):
        dist_input = self._distinguisher.distinguish(self.programs[0], self.programs[1])
        if dist_input is not None:
            logger.info("Distinguishing input: " + dist_input)
            x = input(f'Is "{dist_input}" valid?\n')
            pass
            if x.lower() in yes_values:
                self._decider.add_example([dist_input], True)
                if self._decider.interpreter.eval(self.programs[0], [dist_input]):
                    self.programs = [self.programs[0]]
                else:
                    self.programs = [self.programs[1]]
            elif x.lower() in no_values:
                self._decider.add_example([dist_input], False)
                if not self._decider.interpreter.eval(self.programs[0], [dist_input]):
                    self.programs = [self.programs[0]]
                else:
                    self.programs = [self.programs[1]]
            else:
                logger.info("Invalid answer!")
        else:  # programs are indistinguishable
            logger.info("Programs are indistinguishable")
            # FIXME: Dirty hack!! I'm keeping the "shorter" program :)
            p = min(self.programs, key=lambda p: len(self._printer.eval(p, ["IN"])))
            self.programs = [p]

    def enumerate(self):
        self.num_attempts += 1
        program = self._enumerator.next()
        if program is None: return
        if self._printer is not None:
            logger.debug('Enumerator generated: ' + self._printer.eval(program, ["IN"]))
        else:
            logger.debug(f'Enumerator generated: {program}')

        if self.num_attempts > 0 and self.num_attempts % 1000 == 0:
            logger.info(f'Enumerated {self.num_attempts} programs in {round(time.time() - self.start_time)} seconds.')
            logger.info(f'DSL has {len(self._enumerator.spec.predicates())} predicates.')

        return program
