import operator
import re
from itertools import combinations
from typing import List

import z3

condition_operators = {'<=': operator.le, '>=': operator.ge}
yes_values = {"yes", "valid", "true", "1", "+", "v", "y", "t"}
no_values = {"no", "invalid", "false", "0", "-", "i", "n", "f"}


def nice_time(seconds):
    """ Prints a time in a nice, legible format. """
    seconds = round(seconds)
    m, s = divmod(seconds, 60)
    h, m = divmod(m, 60)
    ret = ''
    if h > 0:
        ret += f'{h}h'
    if m > 0:
        ret += f'{m}m'
    ret += f'{s}s'
    return ret


def is_regex(tentative_regex: str):
    """ Returns true if the argument is a valid python regex, and false otherwise. """
    if len(tentative_regex) == 0:
        return False
    try:
        re.compile(tentative_regex)
        return True
    except re.error:
        return False


def is_int(arg):
    """ Returns True iff arg is a valid integer """
    if isinstance(arg, int):
        return True
    try:
        int(arg)
    except ValueError:
        return False
    return True


def is_float(arg):
    """ Returns True iff arg is a valid float """
    if isinstance(arg, float) or isinstance(arg, int):
        return True
    try:
        float(arg)
    except ValueError:
        return False
    return True


def transpose(lst):
    """ Transposes a matrix. """
    return list(map(list, zip(*lst)))


def all_sublists(iterable, min_len=-1, max_len=-1):
    """ Generate all possible sublists of iterable of size min_len up to max_len. """
    if min_len < 0:
        min_len = 0
    if max_len < 0:
        max_len = len(iterable)

    if min_len == 0:
        yield [[]]
        min_len = 1

    for i in range(len(iterable) + 1):
        for j in range(i + min_len, min(i + max_len + 1, len(iterable) + 1)):
            yield iterable[i:j]


def all_sublists_n(iterable, n):
    if n == 1:
        yield from map(lambda l: [l], all_sublists(iterable, min_len=1))
    else:
        for split_idx in range(1, len(iterable) - (n - 2)):
            for left in all_sublists(iterable[:split_idx], min_len=1):
                if left[-1] != iterable[split_idx - 1]:
                    continue
                for right in all_sublists_n(iterable[split_idx:], n - 1):
                    yield [left] + right


def make_z3_and(args: List):
    if len(args) == 1:
        return args[0]
    return z3.And(args)


def z3_abs(x):
    return z3.If(x >= 0, x, -x)


def conditions_to_str(conditions):
    return ', '.join(map(lambda c: f"${c[0]} {c[1]} {c[2]}", conditions))


def check_conditions(conditions, match):
    max_group_index = max(map(lambda c: int(c.split(" ")[0].replace("$", "", 1)), conditions))
    if len(match.groups()) < max_group_index + 1:
        return False
    for condition in conditions:
        condition = condition.split(" ")
        group_idx = int(condition[0].replace("$", "", 1))
        op = condition_operators[condition[1]]
        value = int(condition[2])
        try:
            string_value = int(match.groups()[group_idx])
        except ValueError: # The text in the regex is not a valid integer
            return True
        if not op(string_value, value):
            return False
    return True
