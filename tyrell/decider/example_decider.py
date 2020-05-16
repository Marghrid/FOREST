import re
from typing import NamedTuple, List, Any

from .decider import Decider
from .result import ok, bad
from ..dsl import Node
from ..interpreter import Interpreter

Example = NamedTuple('Example', [
    ('input', List[Any]),
    ('output', Any)])


class ExampleDecider(Decider):
    _interpreter: Interpreter
    _examples: List[Example]

    def __init__(self, interpreter: Interpreter, examples: List[Example]):
        super().__init__()
        self._interpreter = interpreter
        if len(examples) == 0:
            raise ValueError(
                'ExampleDecider cannot take an empty list of examples')
        self._examples = examples

    @property
    def interpreter(self):
        return self._interpreter

    @property
    def examples(self):
        return self._examples

    @property
    def equal_output(self):
        return self._equal_output

    def add_example(self, ex_in, ex_out):
        new = Example(ex_in, ex_out)
        self.examples.append(new)

    def has_failed_examples(self, program: Node):
        """
        Test whether the given program would fail on any of the examples provided.
        """
        regex = program.children[0]
        regex = self._interpreter.eval(regex, ["dummy"])
        re_compiled = re.compile(regex)
        # return any(
        #     map(lambda x: not self._equal_output(program, x.input, x.output), self._examples)
        # )
        return any(
            map(lambda x: self._match(re_compiled, x.input) != x.output, self._examples)
        )

    def analyze(self, prog):
        '''
        This basic version of analyze() merely interpret the AST and see if it conforms to our examples
        '''
        if self.has_failed_examples(prog):
            return bad()
        else:
            return ok()
    
    def _equal_output(self, program: Node, input, desired_output):
        return desired_output == self._interpreter.eval(program, input)

    def _match(self, re_compiled, input):
        return re_compiled.fullmatch(input[0]) is not None

