import itertools
import re
import time
from abc import ABC
from ..common_substrings import find_all_cs
from ..decider import ExampleDecider, ValidationDecider, Example
from ..distinguisher import Distinguisher
from ..dslBuilder import DSLBuilder
from ..enumerator import GreedyEnumerator, FunnyEnumerator
from ..interpreter import ValidationInterpreter, ValidationPrinter, NodeCounter
from ..logger import get_logger
from ..utils import nice_time

logger = get_logger('tyrell.synthesizer')

yes_values = {"yes", "valid", "true", "1", "+", "v", "y", "t"}
no_values = {"no", "invalid", "false", "0", "-", "i", "n", "f"}


class GreedySynthesizer(ABC):

    def __init__(self, valid_examples, invalid_examples, main_dsl):
        self.max_indistinguishable = 2
        self.indistinguishable = 0
        self._printer = ValidationPrinter()
        self._node_counter = NodeCounter()
        self.valid = valid_examples
        self.invalid = invalid_examples
        self.examples = [Example(x, True) for x in valid_examples] + [Example(x, False) for x in invalid_examples]

        self.main_dsl = main_dsl
        self._distinguisher = Distinguisher()

        self.num_attempts = 0
        self.num_interactions = 0
        self.programs = []
        self.start_time = None

        new_l = len(self.valid[0])
        l = 0
        while new_l != l:
            l = new_l
            self.divide_examples()
            new_l = len(self.valid[0])
            pass
        # divided_valid and divided_invalid are a list of lists. Each list is an example and the lists inside are
        # splits of examples. I want a DSL for each split, with alphabet and the rest computed accordingly.
        self.remove_empties()
        assert all(map(lambda l: len(l) == len(self.valid[0]), self.valid))
        assert len(self.invalid) == 0 or all(map(lambda l: len(l) == len(self.valid[0]), self.invalid))

    @property
    def decider(self):
        return self._decider

    def synthesize(self):
        transposed_valid = list(map(list, zip(*self.valid)))
        assert all(map(lambda l: len(l) == len(transposed_valid[0]), transposed_valid))
        transposed_divided_invalid = list(map(list, zip(*self.invalid)))
        assert all(map(lambda l: len(l) == len(transposed_divided_invalid[0]), transposed_divided_invalid))

        type_validations = ['is_regex'] * len(transposed_valid)
        builder = DSLBuilder(type_validations, self.valid, self.invalid)
        dsls = builder.build()
        self.start_time = time.time()

        if len(self.valid[0]) > 1:
            logger.info("Using GreedyEnumerator.")
            self._decider = ValidationDecider(interpreter=ValidationInterpreter(), examples=self.examples,
                                              split_valid=self.valid)
            for depth in range(3, 10):
                logger.info(f'Synthesizing programs of depth {depth}...')
                self._enumerator = GreedyEnumerator(self.main_dsl, dsls, depth)

                self.try_for_depth()

                if len(self.programs) > 0:
                    logger.info(f'Synthesizer done.\n'
                                f'  Enumerator: {self._enumerator.__class__.__name__}\n'
                                f'  Enumerated: {self.num_attempts}\n'
                                f'  Interactions: {self.num_interactions}\n'
                                f'  Elapsed time: {round(time.time() - self.start_time, 2)}\n'
                                f'  Solution: {self._printer.eval(self.programs[0], ["IN"])}\n'
                                f'  Nodes: {self._node_counter.eval(self.programs[0], [0])}')
                    return self.programs[0]

        else:
            logger.info("Using FunnyEnumerator.")
            self._decider = ValidationDecider(interpreter=ValidationInterpreter(), examples=self.examples)
            sizes = list(itertools.product(range(3, 10), range(1, 10)))
            sizes.sort(key=lambda t: (2 ** t[0] - 1) * t[1])
            for dep, leng in sizes:
                logger.info(f'Synthesizing programs of depth {dep} and length {leng}...')
                self._enumerator = FunnyEnumerator(self.main_dsl, depth=dep, length=leng)

                self.try_for_depth()

                if len(self.programs) > 0:
                    logger.info(f'Synthesizer done.\n'
                                f'  Enumerator: {self._enumerator.__class__.__name__}\n'
                                f'  Enumerated: {self.num_attempts}\n'
                                f'  Interactions: {self.num_interactions}\n'
                                f'  Elapsed time: {round(time.time() - self.start_time, 2)}\n'
                                f'  Solution: {self._printer.eval(self.programs[0], ["IN"])}\n'
                                f'  Nodes: {self._node_counter.eval(self.programs[0], [0])}')
                    return self.programs[0]

        return None

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
                self.programs.append(program)
                if len(self.programs) > 1:
                    self.distinguish()
                if self.indistinguishable >= self.max_indistinguishable:
                    break
            else:
                new_predicates = res.why()
                if new_predicates is not None:
                    for pred in new_predicates:
                        pred_str = self._printer.eval(pred.args[0], ["IN"])
                        logger.debug(f'New predicate: {pred.name} {pred_str}')

            self._enumerator.update(new_predicates)
            # self._enumerator.update(None)
            program = self.enumerate()

    def distinguish(self):
        start_distinguish = time.time()
        dist_input = self._distinguisher.distinguish(self.programs[0], self.programs[1])
        if dist_input is not None:
            logger.info(f'Distinguishing input "{dist_input}" in {round(time.time() - start_distinguish, 2)} seconds')
            self.num_interactions += 1
            valid_answer = False
            # Do not count time spent waiting for user input: add waiting time to start_time.
            interaction_start_time = time.time()
            while not valid_answer:
                x = input(f'Is "{dist_input}" valid?\n')
                if x.lower().rstrip() in yes_values:
                    logger.info(f'"{dist_input}" is valid.')
                    valid_answer = True
                    self._decider.add_example([dist_input], True)
                    if self._decider.interpreter.eval(self.programs[0], [dist_input]):
                        self.programs = [self.programs[0]]
                    else:
                        self.programs = [self.programs[1]]
                        self.indistinguishable = 0
                elif x.lower().rstrip() in no_values:
                    logger.info(f'"{dist_input}" is invalid.')
                    valid_answer = True
                    self._decider.add_example([dist_input], False)
                    if not self._decider.interpreter.eval(self.programs[0], [dist_input]):
                        self.programs = [self.programs[0]]
                    else:
                        self.programs = [self.programs[1]]
                        self.indistinguishable = 0
                else:
                    logger.info(f"Invalid answer {x}! Please answer 'yes' or 'no'.")
            self.start_time += time.time() - interaction_start_time

        else:  # programs are indistinguishable
            logger.info("Programs are indistinguishable")
            self.indistinguishable += 1
            p = min(self.programs, key=lambda p: len(self._printer.eval(p, ["IN"])))
            self.programs = [p]

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

        return program

    def divide_examples(self):
        transposed_valid = list(map(list, zip(*self.valid)))

        for field_idx, field in enumerate(transposed_valid):
            common_substrings = find_all_cs(field)
            if len(common_substrings) == 1 and all(map(lambda f: len(f) == len(common_substrings[0]), field)):
                continue
            if len(common_substrings) > 0:
                for cs in common_substrings:
                    regex = self.build_regex(cs)
                    matches = list(map(lambda ex: re.findall(regex, ex), field))
                    if all(map(lambda m: len(m) == len(matches[0]), matches)):
                        self.split_examples_on(cs, field_idx)

    def build_regex(self, cs):
        if isinstance(cs, str):
            if cs == '.':
                return r'(\.+)'
            elif len(cs) == 1:
                return fr'({cs}+)'
            else:
                return fr'((?:{cs})+)'
        elif isinstance(cs, list):
            pass

    def split_examples_on(self, substring: str, field_idx: int):
        for ex_idx, example in enumerate(self.valid):
            field = example[field_idx]
            rgx = self.build_regex(substring)
            split = re.split(rgx, field, 1)
            example = example[:field_idx] + split + example[field_idx + 1:]
            self.valid[ex_idx] = example
            pass

        remaining_invalid = []
        for ex_idx, example in enumerate(self.invalid):
            field = example[field_idx]
            rgx = self.build_regex(substring)
            split = re.split(rgx, field, 1)
            example = example[:field_idx] + split + example[field_idx + 1:]
            if len(example) == len(self.valid[0]):
                remaining_invalid.append(example)
        self.invalid = remaining_invalid

    def remove_empties(self):
        for field_idx, field in enumerate(self.valid[0]):
            if len(field) == 0:
                # ensure this field is the empty string on all examples
                assert all(map(lambda ex: len(ex[field_idx]) == 0, self.valid + self.invalid))

                for ex in self.valid + self.invalid:
                    ex.pop(field_idx)
