import re
from itertools import combinations


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


def transpose(lst):
    return list(map(list, zip(*lst)))


def powerset(iterable, min_size=-1, max_size=-1):
    if min_size < 0:
        min_size = 0
    if max_size < 0:
        max_size = len(iterable) + 1
    for i in range(min_size, max_size):
        combinations(iterable, i)


def all_sublists(iterable, min_len=-1, max_len=-1):
    if min_len < 0:
        min_len = 0
    if max_len < 0:
        max_len = len(iterable)

    if min_len == 0:
        sublist = [[]]
        min_len = 1
    else:
        sublist = []

    for i in range(len(iterable) + 1):
        for j in range(i + min_len, min(i + max_len + 1, len(iterable) + 1)):
            sublist.append(iterable[i:j])

    return sublist


def all_sublists_gen(iterable, min_len=-1, max_len=-1):
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
        yield from map(lambda l: [l], all_sublists_gen(iterable, min_len=1))
    else:
        for split_idx in range(1, len(iterable) - (n-2)):
            for left in all_sublists_gen(iterable[:split_idx], min_len=1):
                if left[-1] != iterable[split_idx-1]:
                    continue
                for right in all_sublists_n(iterable[split_idx:], n - 1):
                    yield [left] + right


# l = [1, 2, 3, 4, 5]
# all = []
# for a in all_sublists_n(l, 2):
#     if a in all:
#         print("REPEATED")
#     else:
#         all.append(a)
#     print(a)
