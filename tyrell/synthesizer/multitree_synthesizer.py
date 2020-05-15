import itertools
import re
import time
from abc import ABC

from . import MultipleSynthesizer
from ..common_substrings import find_all_cs
from ..decider import ExampleDecider, ValidationDecider, Example
from ..distinguisher import Distinguisher
from ..dslBuilder import DSLBuilder
from ..enumerator import MultiTreeEnumerator, FunnyEnumerator
from ..interpreter import ValidationInterpreter, ValidationPrinter, NodeCounter
from ..logger import get_logger
from ..utils import nice_time

logger = get_logger('tyrell.synthesizer')

yes_values = {"yes", "valid", "true", "1", "+", "v", "y", "t"}
no_values = {"no", "invalid", "false", "0", "-", "i", "n", "f"}


class MultiTreeSynthesizer(MultipleSynthesizer):

    def __init__(self, valid_examples, invalid_examples, main_dsl, ground_truth,
                 pruning=True, auto_interaction=False, force_funny=False):
        super().__init__(valid_examples, invalid_examples, main_dsl, ground_truth,
                         pruning, auto_interaction)
        self.valid = valid_examples
        self.invalid = invalid_examples

        self.main_dsl = main_dsl
        self.special_chars = {'.', '^', '$', '*', '+', '?', '\\', '|', '(', ')',
                              '{', '}', '[', ']', '"'}

        self.force_funny = force_funny

        self.split_examples()

        # divided_valid and divided_invalid are a list of lists. Each list is an
        # example and the lists inside are splits of examples. I want a DSL for each
        # split, with alphabet and the rest computed accordingly.


    def synthesize(self):
        transposed_valid = list(map(list, zip(*self.valid)))
        assert all(map(lambda l: len(l) == len(transposed_valid[0]), transposed_valid))
        transposed_divided_invalid = list(map(list, zip(*self.invalid)))
        assert all(map(lambda l: len(l) == len(transposed_divided_invalid[0]),
                       transposed_divided_invalid))

        type_validations = ['is_regex'] * len(transposed_valid)
        builder = DSLBuilder(type_validations, self.valid, self.invalid)
        dsls = builder.build()

        self.start_time = time.time()

        if len(self.valid[0]) > 1 and not self.force_funny:
            logger.info("Using GreedyEnumerator.")
            self._decider = ValidationDecider(interpreter=ValidationInterpreter(),
                                              examples=self.examples,
                                              split_valid=self.valid)
            for depth in range(3, 10):
                logger.info(f'Synthesizing programs of depth {depth}...')
                self._enumerator = MultiTreeEnumerator(self.main_dsl, dsls, depth)

                self.try_for_depth()

                if len(self.programs) > 0:
                    return self.programs[0]
                elif self.die:
                    return

        else:
            logger.info("Using FunnyEnumerator.")
            self._decider = ValidationDecider(interpreter=ValidationInterpreter(),
                                              examples=self.examples)
            sizes = list(itertools.product(range(3, 10), range(1, 10)))
            sizes.sort(key=lambda t: (2 ** t[0] - 1) * t[1])
            for dep, leng in sizes:
                logger.info(f'Synthesizing programs of depth {dep} and length {leng}...')
                self._enumerator = FunnyEnumerator(self.main_dsl, depth=dep, length=leng)

                self.try_for_depth()

                if len(self.programs) > 0:
                    return self.programs[0]
                elif self.die:
                    return

        return None

    def split_examples(self):
        max_l = max(map(lambda x: len(x[0]), self.valid))
        new_l = len(self.valid[0])
        l = 0
        while new_l != l and l < max_l:
            l = new_l
            transposed_valid = list(map(list, zip(*self.valid)))

            for field_idx, field in enumerate(transposed_valid):
                common_substrings = find_all_cs(field)
                if len(common_substrings) == 1 and all(map(lambda f: len(f) == len(common_substrings[0]), field)):
                    continue

                rec = re.compile(self.build_regex(common_substrings[0]))
                if len(common_substrings) == 1 and all(
                        map(lambda f: rec.fullmatch(f)
                                      is not None, field)):
                    continue
                for cs in common_substrings:
                    rec = re.compile(self.build_regex(cs))
                    matches = list(map(lambda ex: rec.findall(ex), field))
                    if all(map(lambda m: len(m) == len(matches[0]), matches)):
                        self.split_examples_on(cs, field_idx)

            new_l = len(self.valid[0])

        self.remove_empties()

        if not all(map(lambda l: len(l) == len(self.valid[0]), self.valid)):
            return None
        if not len(self.invalid) == 0 or \
               all(map(lambda l: len(l) == len(self.valid[0]), self.invalid)):
            return None

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
                return ret # fr'((?:{cs})+)'
        elif isinstance(cs, list):
            pass

    def split_examples_on(self, substring: str, field_idx: int):
        rec = re.compile(self.build_regex(substring))
        for ex_idx, example in enumerate(self.valid):
            field = example[field_idx]
            split = rec.split(field, 1)
            example = example[:field_idx] + split + example[field_idx + 1:]
            self.valid[ex_idx] = example
            pass

        remaining_invalid = []
        for ex_idx, example in enumerate(self.invalid):
            field = example[field_idx]
            split = rec.split(field, 1)
            example = example[:field_idx] + split + example[field_idx + 1:]
            if len(example) == len(self.valid[0]):
                remaining_invalid.append(example)
        self.invalid = remaining_invalid

    def remove_empties(self):
        for field_idx, field in enumerate(self.valid[0]):
            if len(field) == 0 and all(map(lambda ex: len(ex[field_idx]) == 0, self.valid)):
                # ensure this field is the empty string on all examples
                self.invalid = list(filter(lambda ex: len(ex[field_idx]) == 0, self.invalid))
                for ex in self.valid + self.invalid:
                    ex.pop(field_idx)
