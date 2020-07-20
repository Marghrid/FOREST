import time

from .multiple_synthesizer import MultipleSynthesizer
from ..enumerator import LinesEnumerator
from ..logger import get_logger

logger = get_logger('forest')


class LinesSynthesizer(MultipleSynthesizer):
    def __init__(self, valid_examples, invalid_examples, captures, condition_invalid, dsl,
                 ground_truth, pruning=True, auto_interaction=False):
        super().__init__(valid_examples, invalid_examples, captures, condition_invalid,
                         dsl, ground_truth, pruning, auto_interaction)
        self.max_depth = 6

    def synthesize(self):
        self.start_time = time.time()

        for lines in range(2, self.max_depth + 1):
            self._enumerator = LinesEnumerator(self.dsl, lines)

            self.try_for_depth()

            if len(self.programs) > 0:
                return self.programs[0]
