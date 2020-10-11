import time

from forest.configuration import Configuration
from .multiple_synthesizer import MultipleSynthesizer
from forest.enumerator import LinesEnumerator
from forest.logger import get_logger

logger = get_logger('forest')


class LinesSynthesizer(MultipleSynthesizer):
    def __init__(self, valid_examples, invalid_examples, captured, condition_invalid, dsl,
                 ground_truth, configuration: Configuration):
        super().__init__(valid_examples, invalid_examples, captured, condition_invalid,
                         dsl, ground_truth, configuration)
        self.max_depth = 6

    def synthesize(self):
        self.start_time = time.time()

        for lines in range(2, self.max_depth + 1):
            self._enumerator = LinesEnumerator(self.dsl, lines)

            self.try_for_depth()

            if len(self.solutions) > 0:
                self.terminate()
                return self.solutions[0]
            elif self.die:
                self.terminate()
                return
