import re


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
