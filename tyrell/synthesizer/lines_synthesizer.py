import time

from tyrell.enumerator import LinesEnumerator
from tyrell.logger import get_logger
from tyrell.synthesizer import MultipleSynthesizer

logger = get_logger('tyrell.synthesizer')


class LinesSynthesizer(MultipleSynthesizer):
    def __init__(self, valid_examples, invalid_examples, dsl, ground_truth,  pruning=True, auto_interaction=False):
        super().__init__(valid_examples, invalid_examples, dsl, ground_truth, pruning, auto_interaction)
        self.max_depth = 6

    def synthesize(self):
        logger.info("Using FunnyEnumerator.")
        self.start_time = time.time()

        for lines in range(2, self.max_depth + 1):
            logger.info(f'Synthesizing programs of depth {lines}...')
            self._enumerator = LinesEnumerator(self.dsl, lines)

            self.try_for_depth()

            if len(self.programs) > 0:
                return self.programs[0]
