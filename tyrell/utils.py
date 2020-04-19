import re


def nice_time(seconds):
    m, s = divmod(seconds, 60)
    h, m = divmod(m, 60)
    ret = ''
    if h > 0:
        ret += f'{h}h'
    if m > 0:
        ret += f'{m}m'
    ret += f'{s}s'
    return ret


def is_regex(next_line: str):
    if len(next_line) == 0:
        return False
    try:
        re.compile(next_line)
        return True
    except re.error:
        return False
