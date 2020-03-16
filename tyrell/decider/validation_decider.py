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
from ..dsl import Node
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
        """
        Analyze the reason why a synthesized program fails if it does not pass all the tests.
        """
        if not self.has_failed_examples(program):
            return ok()
        else:
            new_predicates = self.traverse_program(program, self._examples)
            if len(new_predicates) == 0:
                return bad()
            else:
                return bad(why=new_predicates)

    def traverse_program(self, node: Node, examples: List[Example]):
        if self._spec.get_function_production("concat") is None: return []
        new_predicates = []
        valid_exs = list(filter(lambda ex: ex.output == True, examples))
        if node.production.id == self._spec.get_function_production("match").id and node.has_children() \
                and node.children[0].production.id == self._spec.get_function_production("concat").id:
            # Top-level concat
            concat_node = node.children[0]
            assert concat_node.has_children()

            # first child must occur in the beginning of the examples:
            child = concat_node.children[0]
            regex = self.interpreter.eval(child, valid_exs[0])
            # re.match() is not None if zero or more characters at the beginning of string match this regular expression
            matches = map(lambda ex: re.match(regex, ex.input[0]) is not None, valid_exs)

            if not all(matches):
                new_predicate = Predicate("block_first_tree", [child])
                new_predicates.append(new_predicate)

            for child in concat_node.children:
                # if one child has no match in one of the inputs, then it cannot happen as a direct top concat node
                regex = self.interpreter.eval(child, valid_exs[0])
                matches = map(lambda ex: re.search(regex, ex.input[0]) is not None, valid_exs)

                if not all(matches):
                    new_predicate = Predicate("block_tree", [child])
                    new_predicates.append(new_predicate)

        elif node.production.id == self._spec.get_function_production("concat").id:
            regex = self.interpreter.eval(node, valid_exs[0])
            self.check_matches(new_predicates, node, regex, valid_exs)

        elif node.production.id == self._spec.get_function_production("copies").id:
            regex = self.interpreter.eval(node, valid_exs[0])
            self.check_matches(new_predicates, node, regex, valid_exs)

        elif node.production.id == self._spec.get_function_production("kleene").id \
            or node.production.id == self._spec.get_function_production("posit").id:
            regex = self.interpreter.eval(node.children[0], valid_exs[0])
            regex = regex + regex
            self.check_matches(new_predicates, node, regex, valid_exs)

        elif node.production.id == self._spec.get_function_production("option").id:
            atom = self.interpreter.eval(node.children[0], valid_exs[0])
            # if all examples have 'atom' then it should not be option'd
            matches = map(lambda ex: re.search(atom, ex.input[0]) is not None, valid_exs)
            # if they are all true, emit predicate
            if all(matches):
                new_predicate = Predicate("block_subtree", [node])
                new_predicates.append(new_predicate)

        if node.children is not None and len(node.children) > 0:
            for child in node.children:
                return self.traverse_program(child, examples) + new_predicates
        else:
            return new_predicates

    def check_matches(self, new_predicates, node, regex, valid_exs):
        matches = map(lambda ex: re.search(regex, ex.input[0]) is not None, valid_exs)
        no_match = not any(matches)
        if no_match:
            new_predicate = Predicate("block_subtree", [node])
            new_predicates.append(new_predicate)
