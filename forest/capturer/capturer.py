import re

from forest.dsl import Node
from forest.utils import all_sublists, all_sublists_n
from forest.visitor import RegexInterpreter


def elementwise_eq(arg1, arg2):
    for i in range(len(arg1)):
        if arg1[i] != arg2[i]:
            return False
    return True


class Capturer:
    """ capturer is one who, or that which, captures """

    def __init__(self, strings, captures):
        self.strings = strings
        self.captures = captures

    def capture(self, regex: Node):
        if len(self.captures) == 0 or len(self.captures[0]) == 0:
            return []
        nodes = regex.get_leaves()
        # try placing a capture group in each node
        interpreter = RegexInterpreter()
        for sub in all_sublists_n(nodes, len(self.captures[0])):
            regex_str = interpreter.eval(regex, captures=sub)
            compiled_re = re.compile(regex_str)
            if not all(
                    map(lambda s: compiled_re.fullmatch(s[0]) is not None, self.strings)):
                continue
            if all(map(lambda i: elementwise_eq(compiled_re.fullmatch(self.strings[i][0]).groups(), self.captures[i]), range(len(self.strings)))):
                return sub
        return None
