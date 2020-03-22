import re
import time
from abc import ABC
from ..common_substrings import find_all_cs
from ..decider import ExampleDecider, ValidationDecider, Example
from ..distinguisher import Distinguisher
from ..dslBuilder import DSLBuilder
from ..enumerator import GreedyEnumerator
from ..interpreter import Interpreter, ValidationInterpreter
from ..logger import get_logger
from ..utils import nice_time

logger = get_logger('tyrell.synthesizer')

yes_values = {"yes", "valid", "true", "1", "+", "v", "y", "t"}
no_values = {"no", "invalid", "false", "0", "-", "i", "n", "f"}


class GreedySynthesizer(ABC):
    _decider: ValidationDecider
    _printer: Interpreter
    _distinguisher: Distinguisher

    def __init__(self, valid_examples, invalid_examples, main_dsl, printer=None):
        self._printer = printer
        self.valid = valid_examples
        self.invalid = invalid_examples
        self.main_dsl = main_dsl
        self._distinguisher = Distinguisher()

        self.num_attempts = 0
        self.num_interactions = 0
        self.programs = []
        self.start_time = None

        examples = [Example(x, True) for x in valid_examples] + [Example(x, False) for x in invalid_examples]

        self._decider = ValidationDecider(
            interpreter=ValidationInterpreter(),
            examples=examples
        )

    @property
    def decider(self):
        return self._decider

    def synthesize(self):

        divided_valid, divided_invalid = self.divide_examples()

        # divided_valid and divided_invalid are a list of lists. Each list is an example and the lists inside are
        # splits of examples. I want a DSL for each split, with alphabet and the rest computed accordingly.

        assert all(map(lambda l: len(l) == len(divided_valid[0]), divided_valid))
        assert len(divided_invalid) == 0 or all(map(lambda l: len(l) == len(divided_valid[0]), divided_invalid))

        transposed_divided_valid = list(map(list, zip(*divided_valid)))
        assert all(map(lambda l: len(l) == len(transposed_divided_valid[0]), transposed_divided_valid))
        transposed_divided_invalid = list(map(list, zip(*divided_invalid)))
        assert all(map(lambda l: len(l) == len(transposed_divided_invalid[0]), transposed_divided_invalid))

        type_validations = ['is_regex'] * len(transposed_divided_valid)
        builder = DSLBuilder(type_validations, divided_valid, divided_invalid)
        dsls = builder.build()
        self.start_time = time.time()

        for depth in range(3,10):
            logger.info(f'Synthesizing programs of depth {depth}...')
            self._enumerator = GreedyEnumerator(self.main_dsl, dsls, depth)

            program = self.enumerate()

            while program is not None:
                new_predicates = None

                res = self._decider.analyze(program)

                if res.is_ok():  # program satisfies I/O examples
                    logger.info(
                        f'Program accepted after {self.num_attempts} attempts '
                        f'and {round(time.time() - self.start_time)} seconds:')
                    logger.info(self._printer.eval(program, ["IN"]))
                    self.programs.append(program)
                    if len(self.programs) > 1:
                        self.distinguish()
                else:
                    new_predicates = res.why()
                    if new_predicates is not None:
                        for pred in new_predicates:
                            pred_str = self._printer.eval(pred.args[0], ["IN"])
                            logger.debug(f'New predicate: {pred.name} {pred_str}')

                self._enumerator.update(new_predicates)
                program = self.enumerate()

            if len(self.programs) > 0:
                logger.info(f'Synthesizer done after\n'
                            f'  {self.num_attempts} attempts,\n'
                            f'  {self.num_interactions} interactions,\n'
                            f'  and {round(time.time() - self.start_time)} seconds')
                return self.programs[0]



        return None

    def divide_examples(self):
        transposed_valid = list(map(list, zip(*self.valid)))
        assert len(transposed_valid) == 1
        transposed_valid = transposed_valid[0]

        transposed_invalid = list(map(list, zip(*self.invalid)))
        transposed_invalid = transposed_invalid[0]

        substrings = find_all_cs(transposed_valid)
        if len(substrings) == 0:
            return self.valid, self.invalid

        # substrings occur in all valid examples.
        # how many times do they show up in the examples? is it always the same number of times?
        dividing_substrings = []
        for substr in substrings:
            if substr == '.':
                single_rgx = r'\.+|'
            elif len(substr) == 1:
                single_rgx = fr'({substr}+)'
            else:
                single_rgx = fr'((?:{substr})+)'
            matches = list(map(lambda ex: re.findall(single_rgx, ex), transposed_valid))
            if all(map(lambda m: len(m) == len(matches[0]), matches)):
                # it appears the same number of times in each string
                dividing_substrings.append(substr)

            matches_valid = re.findall(single_rgx, transposed_valid[0])
            self.invalid = list(filter(lambda x: len(matches_valid) == len(re.findall(single_rgx, x[0])), self.invalid))

        if len(dividing_substrings) == 0:
            return self.valid, self.invalid

        all_substr_rgx = '('
        for substr in dividing_substrings:
            if substr == '.':
                all_substr_rgx += r'\.+|'
            elif len(substr) == 1:
                all_substr_rgx += f'{substr}+|'
            else:
                all_substr_rgx += f'(?:{substr})+|'
        all_substr_rgx = all_substr_rgx[:-1]
        all_substr_rgx += ')'

        divided_valid = []

        for example in transposed_valid:
            split = re.split(all_substr_rgx, example)
            if len(split[0]) == 0:
                split.pop(0)
            if len(split[-1]) == 0:
                split.pop(-1)
            divided_valid.append(split)

        for ss in dividing_substrings:
            if ss == '.':
                single_rgx = r'\.+|'
            elif len(ss) == 1:
                single_rgx = f'({ss}+)'
            else:
                single_rgx = f'((?:{ss})+)'

            matches_valid = re.findall(single_rgx, transposed_valid[0])
            self.invalid = list(filter(lambda x: len(matches_valid) == len(re.findall(single_rgx, x[0])), self.invalid))

        if len(self.invalid) == 0:
            return divided_valid, []

        transposed_invalid = list(map(list, zip(*self.invalid)))
        transposed_invalid = transposed_invalid[0]
        divided_invalid = []
        for example in transposed_invalid:
            split = re.split(all_substr_rgx, example)
            if len(split[0]) == 0 and split[1] == divided_valid[0][0]:
                split.pop(0)
            if len(split[-1]) == 0 and split[-2] == divided_valid[0][-1]:
                split.pop(-1)
            divided_invalid.append(split)
        return divided_valid, divided_invalid

    def distinguish(self):
        dist_input = self._distinguisher.distinguish(self.programs[0], self.programs[1])
        if dist_input is not None:
            logger.info("Distinguishing input: " + dist_input)
            self.num_interactions += 1
            valid_answer = False
            while not valid_answer:
                x = input(f'Is "{dist_input}" valid?\n')
                if x.lower() in yes_values:
                    valid_answer = True
                    self._decider.add_example([dist_input], True)
                    if self._decider.interpreter.eval(self.programs[0], [dist_input]):
                        self.programs = [self.programs[0]]
                    else:
                        self.programs = [self.programs[1]]
                elif x.lower() in no_values:
                    valid_answer = True
                    self._decider.add_example([dist_input], False)
                    if not self._decider.interpreter.eval(self.programs[0], [dist_input]):
                        self.programs = [self.programs[0]]
                    else:
                        self.programs = [self.programs[1]]
                else:
                    logger.info("Invalid answer! Please answer 'yes' or 'no'.")
        else:  # programs are indistinguishable
            logger.info("Programs are indistinguishable")
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
