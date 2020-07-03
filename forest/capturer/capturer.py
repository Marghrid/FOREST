import re

from forest.dsl import Node
from forest.visitor import RegexInterpreter


class Capturer:
    """ capturer is one who, or that which, captures """

    def __init__(self, strings, captures):
        self.strings = strings
        self.captures = captures

    def capture(self, regex: Node):
        if len(self.captures) == 0 or len(self.captures[0]) == 0:
            return []
        nodes = regex.get_subtree()
        # try placing a capture group in each node
        interpreter = RegexInterpreter()
        for node in nodes:
            regex_str = interpreter.eval(regex, captures=[node])
            compiled_re = re.compile(regex_str)
            if all(map(lambda i: compiled_re.fullmatch(self.strings[i][0]).groups()[0] \
                                 == self.captures[i][0], range(len(self.strings)))):
                return [node]
        return None
