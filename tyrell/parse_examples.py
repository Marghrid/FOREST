import re

from tyrell.logger import get_logger

logger = get_logger('tyrell')


def parse_file(filename):
    logger.info("Parsing examples from file " + filename)
    invalid_exs = []
    valid_exs = []
    with open(filename, "r") as in_file:
        next_line = in_file.readline()
        while next_line and not next_line.startswith("++"):
            next_line = in_file.readline()

        next_line = in_file.readline()  # skip line with "++"
        while next_line and not next_line.startswith("--"):
            next_line = next_line.rstrip()
            exs = read_example(filename, next_line)
            valid_exs.extend(exs)
            next_line = in_file.readline()

        next_line = in_file.readline()  # skip line with "--"
        while next_line:
            next_line = next_line.rstrip()
            exs = read_example(filename, next_line)
            invalid_exs.extend(exs)
            next_line = in_file.readline()

    return valid_exs, invalid_exs


def parse_resnax(filename):
    logger.info("Parsing examples from file " + filename)

    invalid_exs = []
    valid_exs = []
    with open(filename, "r") as in_file:
        next_line = in_file.readline().rstrip()
        while next_line is not None and not '// example' in next_line:
            print(next_line)
            next_line = in_file.readline().rstrip()

        next_line = in_file.readline().rstrip()  # skip line with "// examples"
        while next_line and '// gt' not in next_line:
            next_line = in_file.readline().rstrip()

            ex, valid = read_resnax_example(next_line)
            if ex is None:
                continue
            if valid:
                valid_exs.append([ex])
            else:
                invalid_exs.append([ex])

    return valid_exs, invalid_exs


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
