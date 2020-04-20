import re
from typing import Tuple
from .example_base_decider import Example, ExampleDecider
from .result import ok, bad
from ..dsl import Node
from ..interpreter import Interpreter
from ..logger import get_logger
from ..spec import Production, TyrellSpec, Predicate
from ..spec.expr import *

logger = get_logger('tyrell.synthesizer.constraint')


class ValidationDecider(ExampleDecider):

    def __init__(self, interpreter: Interpreter, examples: List[Example], split_valid = None):
        super().__init__(interpreter, examples)
        self.already_must_occur = set()
        self.valid_exs = list(filter(lambda ex: ex.output == True, examples))
        self.split_valid = split_valid

        # Ensure the split examples all have the same number of substrings
        assert self.split_valid is None or all(map(lambda x: len(x) == len(self.split_valid[0]), self.split_valid))

    def analyze(self, program: Node):
        """
        Analyze the reason why a synthesized program fails if it does not pass all the tests.
        """
        if not self.has_failed_examples(program):
            return ok()
        else:
            new_predicates = []
            if program.production.is_function() and program.production.name == "match":
                new_predicates = self.traverse_regex(program.children[0])
            else:
                new_predicates = self.traverse_program(program, self._examples)

            if len(new_predicates) == 0:
                return bad()
            else:
                return bad(why=new_predicates)

    def traverse_regex(self, node: Node):
        """ Analyze regex programs, generated by Greedy or Funny Synthesizer """
        new_predicates = []
        # the top node is always concat if the program is generated by greedy_enumerator or funny_enumerator

        assert self.split_valid is None or len(node.children) == len(self.split_valid[0]), f"{len(node.children)} and {len(self.split_valid[0])}"
        for tree_idx, child in enumerate(node.children):
            if node.name == "concat" and node.has_children():
                # if one child has no match in one of the inputs, then it cannot happen as a direct top concat node
                regex = self.interpreter.eval(child, self.valid_exs[0])
                matches = map(lambda ex: re.search(regex, ex.input[0]) is not None, self.valid_exs)

                if not all(matches):
                    new_predicate = Predicate("block_tree", [child, tree_idx])
                    new_predicates.append(new_predicate)

                if self.split_valid is not None:
                    assert len(node.children) == len(self.split_valid[0])
                    matches = map(lambda ex: re.fullmatch(regex, ex[tree_idx]) is not None, self.split_valid)
                    if not all(matches):
                        new_predicate = Predicate("block_tree", [child, tree_idx])
                        new_predicates.append(new_predicate)

            new_predicates += self.traverse_regex_rec(node.children[tree_idx], tree_idx)

        return new_predicates

    def traverse_regex_rec(self, node, tree_idx):
        new_predicates = []
        production = node.production
        if production.is_function():
            if production.name == "concat":
                regex = self.interpreter.eval(node, self.valid_exs[0])
                new_predicate = self.check_matches(node, regex, tree_idx)
                if new_predicate is not None:
                    new_predicates.append(new_predicate)

            elif production.name == "range":
                regex = self.interpreter.eval(node, self.valid_exs[0])
                arg = node.args[1].data.split(',')
                assert len(arg) == 2
                # arg = (int(arg[0]), int(arg[1]))
                regex0 = re.sub('\{.*\}', '{' + arg[0] + '}', regex, 1)
                new_predicate = self.check_matches(node, regex0, tree_idx)
                if new_predicate is not None:
                    new_predicates.append(new_predicate)

                regex1 = re.sub('\{.*\}', '{' + arg[1] + '}', regex, 1)
                new_predicate = self.check_matches(node, regex1, tree_idx)
                if new_predicate is not None:
                    new_predicates.append(new_predicate)

            elif production.name == "kleene" or production.name == "posit":
                regex = self.interpreter.eval(node.children[0], self.valid_exs[0])
                regex = regex + regex
                new_predicate = self.check_matches(node, regex, tree_idx)
                if new_predicate is not None:
                    new_predicates.append(new_predicate)

            elif production.name == "re":
                char_node = node.children[0]
                assert (char_node.is_enum() and char_node.type.name == "Char")
                st = str(char_node.data)
                # FIXME: What if char is always present but it is part of a char class? Then it can be the char class
                #  that must occur.
                if all(map(lambda x: re.search(st, x.input[0]) is not None, self.valid_exs)) \
                        and '[' not in st and st not in self.already_must_occur:
                    self.already_must_occur.add(st)
                    new_predicate = Predicate("char_must_occur", [char_node, tree_idx])
                    new_predicates.append(new_predicate)

        if node.has_children():
            for child in node.children:
                child_traverse = self.traverse_regex_rec(child, tree_idx)
                if child_traverse is not None and len(child_traverse) > 0:
                    return child_traverse

            return new_predicates
        else:
            return new_predicates

    def check_matches(self, node, regex, tree_idx):
        matches = map(lambda ex: re.search(regex, ex.input[0]) is not None, self.valid_exs)
        no_match = not any(matches)
        if no_match:
            new_predicate = Predicate("block_subtree", [node, tree_idx])
            return new_predicate

    def traverse_program(self, program, examples):
        return []
