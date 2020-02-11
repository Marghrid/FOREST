import re
from typing import (
    Tuple,
    Mapping,
    MutableMapping,
    Any,
    Callable
)

from .example_base_decider import Example, ExampleDecider
from .result import ok, bad
from ..interpreter import Interpreter
from ..logger import get_logger
from ..spec import Production, TyrellSpec, Predicate
from ..spec.expr import *

logger = get_logger('tyrell.synthesizer.constraint')
ImplyMap = Mapping[Tuple[Production, Expr], List[Production]]
MutableImplyMap = MutableMapping[Tuple[Production, Expr], List[Production]]


class ValidationDecider(ExampleDecider):

    def __init__(self,
                 spec: TyrellSpec,
                 interpreter: Interpreter,
                 examples: List[Example],
                 equal_output: Callable[[Any, Any], bool] = lambda x, y: x == y):
        super().__init__(interpreter, examples, equal_output)
        self._spec = spec

    def analyze(self, program):
        '''
        This version of analyze() tries to analyze the reason why a synthesized program fails, if it does not pass all the tests.
        '''
        if not self.has_failed_examples(program):
            return ok()
        else:
            new_predicates = self.traverse(program, self._examples)
            if len(new_predicates) == 0:
                return bad()
            else:
                return bad(why=new_predicates)

    def traverse(self, node, examples: List[Example]):
        # print("node prod", node.production)
        # print("spec prod", self._spec.get_function_production("concat"))
        new_predicates = []
        if node.production.id == self._spec.get_function_production("concat").id and all(
                [child.production.id == self._spec.get_function_production("re").id for child in node.children]):
            # found a simple concat: the direct concatenation of 2 atoms
            atoms = [child.children[0].data for child in node.children]
            regex = ''.join(atoms)

            # if none of valid examples have this pattern, then it is not feasible
            valid_exs = list(filter(lambda ex: ex.output == True, examples))
            matches = [re.search(regex, ex.input[0]) is not None for ex in valid_exs]
            no_match = not any(matches)

            if no_match:
                # none of valid examples have this pattern -> it is not feasible
                # TODO: block all models containing this concat
                print(f"block concat({atoms})")
                new_predicate = Predicate("do_not_concat", atoms)
                new_predicates.append(new_predicate)

        if node.children is not None and len(node.children) > 0:
            for child in node.children:
                return self.traverse(child, examples) + new_predicates
        else:
            return new_predicates
