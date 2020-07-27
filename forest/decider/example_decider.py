import re
from typing import NamedTuple, List, Any

import z3

from .decider import Decider
from .result import ok, bad
from ..dsl import Node
from ..visitor import Interpreter, ToZ3

Example = NamedTuple('Example', [
    ('input', List[Any]),
    ('output', Any)])


class ExampleDecider(Decider):

    def __init__(self, interpreter: Interpreter, examples: List[Example]):
        super().__init__()
        self._interpreter = interpreter
        self._to_z3 = ToZ3()
        self.use_smt = False
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

    def add_example(self, ex_in, ex_out):
        """ Add new example to specification """
        new = Example(ex_in, ex_out)
        self.examples.append(new)

    def has_failed_examples(self, regex: Node):
        """
        Test whether the given program would fail on any of the examples provided.
        """
        if not self.use_smt:
            regex = self._interpreter.eval(regex)
            re_compiled = re.compile(regex)
            return any(
                map(lambda x: self._match(re_compiled, x.input) != x.output,
                    self._examples)
            )
        else:
            regex_z3 = self._to_z3.eval(regex)
            z3_solver = z3.Solver()
            big_and = []
            for x in self._examples:
                if x.output:
                    big_and.append(z3.InRe(x.input[0], regex_z3))
                else:
                    big_and.append(z3.Not(z3.InRe(x.input[0], regex_z3)))
            z3_solver.add(z3.And(big_and))

            return z3_solver.check() == z3.unsat

    def analyze(self, prog):
        '''
        This basic version of analyze() merely interprets the AST and sees if it conforms
        to our examples
        '''
        if self.has_failed_examples(prog):
            return bad()
        else:
            return ok()

    def _match(self, re_compiled, input):
        return re_compiled.fullmatch(input[0]) is not None
