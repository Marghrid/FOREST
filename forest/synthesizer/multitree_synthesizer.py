import itertools
import re
import time
from copy import deepcopy

from forest.configuration import Configuration
from forest.decider import RegexDecider
from forest.dsl.dsl_builder import DSLBuilder
from forest.enumerator import StaticMultiTreeEnumerator, DynamicMultiTreeEnumerator
from forest.logger import get_logger
from forest.stats import Statistics
from forest.utils import transpose, find_all_cs
from forest.visitor import RegexInterpreter
from .multiple_synthesizer import MultipleSynthesizer

logger = get_logger('forest')
stats = Statistics.get_statistics()


class MultiTreeSynthesizer(MultipleSynthesizer):
    def __init__(self, valid_examples, invalid_examples, captured, condition_invalid,
                 main_dsl, ground_truth, configuration: Configuration = Configuration()):
        super().__init__(valid_examples, invalid_examples, captured, condition_invalid,
                         main_dsl, ground_truth, configuration=configuration)
        self.main_dsl = main_dsl
        self.special_chars = {'.', '^', '$', '*', '+', '?', '\\', '|', '(', ')',
                              '{', '}', '[', ']', '"'}

    def synthesize(self):
        self.start_time = time.time()
        try:
            valid, invalid = self.split_examples()
        except:
            valid = None
            invalid = None

        if valid is not None and len(valid[0]) > 1 and not self.configuration.force_dynamic:
            self._decider = RegexDecider(interpreter=RegexInterpreter(),
                                         valid_examples=self.valid, invalid_examples=self.invalid,
                                         split_valid=valid)

            self.valid = valid
            self.invalid = invalid

            assert all(map(lambda l: len(l) == len(self.valid[0]), self.valid))
            assert all(map(lambda l: len(l) == len(self.invalid[0]), self.invalid))

            type_validations = ['regex'] * len(self.valid[0])
            builder = DSLBuilder(type_validations, self.valid, self.invalid)
            dsls = builder.build()

            for depth in range(3, 10):
                self._enumerator = StaticMultiTreeEnumerator(self.main_dsl, dsls, depth)
                depth_start = time.time()
                self.try_for_depth()
                stats.per_depth_times[depth] = time.time() - depth_start
                if len(self.solutions) > 0:
                    self.terminate()
                    return self.solutions[0]
                elif self.configuration.die:
                    self.terminate()
                    return

        else:
            self._decider = RegexDecider(RegexInterpreter(), self.valid, self.invalid)
            sizes = list(itertools.product(range(3, 10), range(1, 10)))
            sizes.sort(key=lambda t: (2 ** t[0] - 1) * t[1])
            for dep, length in sizes:
                self._enumerator = DynamicMultiTreeEnumerator(self.main_dsl, depth=dep,
                                                              length=length)
                depth_start = time.time()
                self.try_for_depth()
                stats.per_depth_times[(dep, length)] = time.time() - depth_start

                if len(self.solutions) > 0:
                    self.terminate()
                    return self.solutions[0]
                elif self.configuration.die:
                    self.terminate()
                    return

        return None

    def split_examples(self):
        max_l = max(map(lambda x: len(x[0]), self.valid))
        new_l = len(self.valid[0])
        l = 0
        valid = deepcopy(self.valid)
        invalid = deepcopy(self.invalid)
        while new_l != l and l < max_l:
            l = new_l
            transposed_valid = transpose(valid)

            for field_idx, field in enumerate(transposed_valid):
                common_substrings = find_all_cs(field)
                if len(common_substrings) == 1:
                    rec = re.compile(self.build_regex(common_substrings[0]))
                    if all(map(lambda f: rec.fullmatch(f) is not None, field)):
                        continue
                    if all(map(lambda f: len(f) == len(common_substrings[0]), field)):
                        continue
                for cs in common_substrings:
                    rec = re.compile(self.build_regex(cs))
                    matches = list(map(lambda ex: rec.findall(ex), field))
                    if all(map(lambda m: len(m) == len(matches[0]), matches)):
                        valid, invalid = self.split_examples_on(valid, invalid, cs,
                                                                field_idx)

            new_l = len(valid[0])

        valid, invalid = self.remove_empties(valid, invalid)

        if not all(map(lambda l: len(l) == len(valid[0]), valid)):
            return None, None
        if len(invalid) > 0 and not all(map(lambda l: len(l) == len(valid[0]), invalid)):
            return None, None

        return valid, invalid

    def split_examples_on(self, valid, invalid, substring: str, field_idx: int):
        rec = re.compile(self.build_regex(substring))
        for ex_idx, example in enumerate(valid):
            field = example[field_idx]
            split = rec.split(field, 1)
            example = example[:field_idx] + split + example[field_idx + 1:]
            valid[ex_idx] = example
            pass

        remaining_invalid = []
        for ex_idx, example in enumerate(invalid):
            field = example[field_idx]
            split = rec.split(field, 1)
            example = example[:field_idx] + split + example[field_idx + 1:]
            if len(example) == len(valid[0]):
                remaining_invalid.append(example)
        invalid = remaining_invalid

        return valid, invalid

    def build_regex(self, cs):
        if isinstance(cs, str):
            if cs in self.special_chars:
                return f'(\\{cs}+)'
            elif len(cs) == 1:
                return fr'({cs}+)'
            else:
                ret = ''
                ret = '((?:'
                for char in cs:
                    if char in self.special_chars:
                        ret += "\\"
                    ret += char
                ret += ")+)"
                return ret  # fr'((?:{cs})+)'
        elif isinstance(cs, list):
            pass

    def remove_empties(self, valid, invalid):
        for field_idx, field in enumerate(valid[0]):
            if len(field) == 0 and all(
                    map(lambda ex: len(ex[field_idx]) == 0, valid)):
                # ensure this field is the empty string on all examples
                invalid = list(
                    filter(lambda ex: len(ex[field_idx]) == 0, invalid))
                for ex in valid + invalid:
                    ex.pop(field_idx)
        return valid, invalid
