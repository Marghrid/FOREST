import re
from typing import Tuple, List

from termcolor import colored

from forest.dsl.dsl_builder import DSLBuilder
from forest.logger import get_logger
from forest.spec import TyrellSpec
from forest.utils import is_regex

logger = get_logger('forest')


def show(valid, invalid, condition_invalid, ground_truth: str):
    print(len(valid), "valid examples:")
    max_len = max(map(lambda x: sum(map(len, x)) + 2 * len(x), valid))
    max_len = max(max_len, 6)
    line_len = 0
    for ex in valid:
        s = ', '.join(ex).center(max_len)
        line_len += len(s)
        print(colored(s, "blue"), end='  ')
        if line_len > 70:
            line_len = 0
            print()
    print()

    print(len(invalid), "invalid examples:")
    max_len = max(map(lambda x: len(x[0]), invalid))
    max_len = max(max_len, 6)
    line_len = 0
    for ex in invalid:
        s = f'{ex[0]}'.center(max_len)
        line_len += len(s)
        print(colored(s, "red"), end='  ')
        if line_len > 70:
            line_len = 0
            print()
    print()

    if len(condition_invalid) > 0:
        print(len(condition_invalid), "condition invalid examples:")
        max_len = max(map(lambda x: len(x[0]), condition_invalid))
        max_len = max(max_len, 6)
        line_len = 0
        for ex in condition_invalid:
            s = f'{ex[0]}'.center(max_len)
            line_len += len(s)
            print(colored(s, "magenta"), end='  ')
            if line_len > 70:
                line_len = 0
                print()
        print()
    else:
        print("No condition invalid examples.")
    print("Ground truth:")
    print(colored(ground_truth, "green"))


def preprocess(valid, invalid, cond_invalid, sketch=False) \
        -> Tuple[TyrellSpec, List[List], List[List], List[List], List[List], List[str]]:
    """  returns dsl, valid_examples, invalid_examples, captures, and type_validation """
    type_validation = ["regex"]
    if len(valid) == 0:
        raise ValueError("No valid examples!")
    if isinstance(valid[0], str):
        valid = list(map(lambda v: [v], valid))
    if isinstance(invalid[0], str):
        invalid = list(map(lambda v: [v], invalid))
    if cond_invalid and isinstance(cond_invalid[0], str):
        cond_invalid = list(map(lambda v: [v], cond_invalid))
    # logger.info("Assuming types: " + str(type_validation))
    captures = list(map(lambda x: x[1:], valid))
    valid = list(map(lambda x: [x[0]], valid))
    builder = DSLBuilder(type_validation, valid, invalid, sketch)
    dsl = builder.build()[0]

    return dsl, valid, invalid, cond_invalid, captures, type_validation


def parse_file(filename):
    logger.info("Parsing examples from file " + filename)
    invalid_exs = []
    valid_exs = []
    condition_invalid_exs = []
    ground_truth = ''
    with open(filename, "r") as in_file:
        next_line = in_file.readline()
        while next_line and not next_line.startswith("++"):
            # discard comments before examples
            next_line = in_file.readline()

        next_line = in_file.readline()  # skip line with "++"
        while next_line and not next_line.startswith("--"):
            next_line = next_line.rstrip()
            exs = read_example(filename, next_line)
            valid_exs.extend(exs)
            next_line = in_file.readline()

        next_line = in_file.readline()  # skip line with "--"
        while next_line and not next_line.startswith("+-") and not next_line.startswith("**"):
            next_line = next_line.rstrip()
            exs = read_example(filename, next_line)
            invalid_exs.extend(exs)
            next_line = in_file.readline()

        if next_line.startswith("+-"):
            next_line = in_file.readline()  # skip line with "+-"
            while next_line and not next_line.startswith("**"):
                next_line = next_line.rstrip()
                exs = read_example(filename, next_line)
                condition_invalid_exs.extend(exs)
                next_line = in_file.readline()

        while next_line:
            next_line = next_line.rstrip()
            if is_regex(next_line):
                ground_truth = next_line
                break
            next_line = in_file.readline()

    return valid_exs, invalid_exs, condition_invalid_exs, ground_truth


def parse_resnax(filename):
    logger.info("Parsing examples from file " + filename)

    invalid_exs = []
    valid_exs = []
    ground_truth_next = False
    ground_truth = ''
    with open(filename, "r") as in_file:
        for next_line in in_file:
            next_line = next_line.rstrip()
            if ground_truth_next:
                ground_truth = next_line
                ground_truth_next = False
                continue
            ex, valid = read_resnax_example(next_line)
            if ex is None:
                if len(next_line) > 2 and not next_line.startswith("//"):
                    print(" ", next_line)
                elif next_line.startswith('// gt') or next_line.startswith(
                        '// ground truth'):
                    ground_truth_next = True
                continue
            if valid:
                valid_exs.append([ex])
            else:
                invalid_exs.append([ex])

    return valid_exs, invalid_exs, ground_truth


def read_example(filename, next_line):
    exs = []
    if len(next_line) > 0:
        if "AlphaRegex" not in filename:
            exs = [[i.strip() for i in next_line.split(',')]]
        else:
            exs = read_AlphaRegex_example(next_line)
    return exs


def read_AlphaRegex_example(next_line):
    exs = []
    if 'X' not in next_line:
        exs.append([next_line])
    else:
        with_x = [next_line]
        while len(with_x) > 0:
            n = with_x.pop(0)
            new0 = n.replace("X", "0", 1)
            new1 = n.replace("X", "1", 1)
            if "X" in new0:
                with_x.append(new0)
                with_x.append(new1)
            else:
                exs.append([new0])
                exs.append([new1])
    return exs


def read_resnax_example(next_line):
    match = re.fullmatch(r'"(.*)",([+\-])', next_line)
    if match is None:
        return None, None

    ex = match.groups()[0]
    valid = match.groups()[1] == '+'
    return ex, valid
