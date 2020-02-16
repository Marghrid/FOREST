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
                 examples: List[Example]):
        super().__init__(interpreter, examples)
        self._spec = spec

    def analyze(self, program):
        '''
        Analyze the reason why a synthesized program fails if it does not pass all the tests.
        '''
        if not self.has_failed_examples(program):
            return ok()
        else:
            new_predicates = self.traverse_program(program, self._examples)
            if len(new_predicates) == 0:
                return bad()
            else:
                return bad(why=new_predicates)

    def traverse_program(self, node, examples: List[Example]):
        # print("node prod", node.production)
        # print("spec prod", self._spec.get_function_production("concat"))
        new_predicates = []
        if node.production.id == self._spec.get_function_production("concat").id:
            # if none of valid examples have this pattern, then it is not feasible
            valid_exs = list(filter(lambda ex: ex.output == True, examples))
            regex = self.interpreter.eval(node, valid_exs[0])

            matches = [re.search(regex, ex.input[0]) is not None for ex in valid_exs]
            no_match = not any(matches)

            if no_match:
                new_predicate = Predicate("do_not_concat", [node])
                new_predicates.append(new_predicate)

        if (node.production.id == self._spec.get_function_production("kleene").id
            or node.production.id == self._spec.get_function_production("posit").id)\
                and node.children[0].production.id == self._spec.get_function_production("re").id:
            # found a simple kleene or simple posit: directly from an atom
            atom = node.children[0].children[0].data
            regex = atom + atom

            # if none of valid examples have this pattern repeated twice, then it is not feasible
            valid_exs = list(filter(lambda ex: ex.output == True, examples))
            matches = [re.search(regex, ex.input[0]) is not None for ex in valid_exs]
            no_match = not any(matches)

            if no_match:
                new_predicate = Predicate("do_not_kleene", [atom])
                new_predicates.append(new_predicate)
                new_predicate = Predicate("do_not_posit", [atom])
                new_predicates.append(new_predicate)
        if node.production.id == self._spec.get_function_production("copies").id \
                and node.children[0].production.id == self._spec.get_function_production("re").id:
            # found a simple kleene or simple posit: directly from an atom
            re_atom = node.children[0].children[0].data
            count = int(node.children[1].data)
            regex = re_atom * count

            # if none of valid examples have this pattern repeated twice, then it is not feasible
            valid_exs = list(filter(lambda ex: ex.output == True, examples))
            matches = [re.search(regex, ex.input[0]) is not None for ex in valid_exs]
            no_match = not any(matches)

            if no_match:
                new_predicate = Predicate("do_not_copies", [re_atom, count])
                new_predicates.append(new_predicate)

        if node.children is not None and len(node.children) > 0:
            for child in node.children:
                return self.traverse_program(child, examples) + new_predicates
        else:
            return new_predicates

    # def _equal_output(self, program, input, desired_output):
    #     try:
    #         output = self._interpreter.eval(program, input)
    #         return output == desired_output
    #     except Exception as e:
    #         print("exception", e)
    #         return False == desired_output
