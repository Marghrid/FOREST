from abc import ABC, abstractmethod
from collections import deque
from typing import Any

import z3

from .ast import AST, ASTNode
from ..dsl import Node, AtomNode
from ..logger import get_logger

logger = get_logger('forest')


class RegexEnumerator(ABC):

    @abstractmethod
    def __init__(self, dsl):
        z3.Z3_DEBUG = False
        self.z3_solver = z3.Solver()
        self.variables = {}
        self.variables_fun = []
        self.trees = []
        self.nodes = []
        self.model = None

        self.dsl = dsl
        self.max_children = self.max_children()
        self._get_range_values()

    @abstractmethod
    def update(self, info: Any = None) -> None:
        '''
        Update the internal state of the enumerator. This can be useful when trying to prune the search space.
        By default, it does nothing.
        '''
        raise NotImplementedError

    @staticmethod
    def build_k_tree(children, depth, tree_id):
        """ Builds a K-tree that will contain the program """
        tree = AST(tree_id)
        root = ASTNode(1, 1, None, tree_id)
        nb = 1
        tree.head = root
        d = deque()
        d.append(root)
        tree.nodes.append(root)
        while len(d) != 0:
            current = d.popleft()
            current.children = []
            for x in range(0, children):
                nb += 1
                c = ASTNode(nb, current.depth + 1, None, tree_id)
                tree.nodes.append(c)
                current.children.append(c)
                if c.depth < depth:
                    d.append(c)
        return tree

    def max_children(self) -> int:
        """ Finds the maximum number of children in the productions """
        return max(map(lambda p: len(p.rhs), self.dsl.productions()))

    def _get_range_values(self):
        """ Organizes DSL's range values into dictionaries based on their upper and
        lower bounds """
        range_val_ty = self.dsl.get_type("RangeLit")
        if range_val_ty is None:
            return
        range_val_enum = self.dsl.get_productions_with_lhs(range_val_ty)
        self.range_lower_bounds = {}
        self.range_upper_bounds = {}
        for range_val in range_val_enum:
            data = range_val.rhs[0]
            data = data.split(',')
            if len(data) < 2:  # probably sketches
                break
            range_node = AtomNode(range_val)
            if data[0] not in self.range_lower_bounds:
                self.range_lower_bounds[data[0]] = []
            self.range_lower_bounds[data[0]].append(range_node)

            if data[1] not in self.range_upper_bounds:
                self.range_upper_bounds[data[1]] = []
            self.range_upper_bounds[data[1]].append(range_node)

    @staticmethod
    def _check_arg_types(pred, python_tys):
        if pred.num_args() < len(python_tys):
            msg = 'Predicate "{}" must have at least {} arguments. Only {} is found.'.format(
                pred.name, len(python_tys), pred.num_args())
            raise ValueError(msg)
        for index, (arg, python_ty) in enumerate(zip(pred.args, python_tys)):
            if not isinstance(arg, python_ty):
                msg = 'Argument {} of predicate {} has unexpected type.'.format(
                    index, pred.name)
                raise ValueError(msg)

    @abstractmethod
    def _resolve_is_not_parent_predicate(self, pred):
        raise NotImplementedError

    @abstractmethod
    def _resolve_block_subtree_predicate(self, pred):
        raise NotImplementedError

    @abstractmethod
    def _resolve_block_tree_predicate(self, pred):
        raise NotImplementedError

    @abstractmethod
    def _resolve_block_first_tree_predicate(self, pred):
        raise NotImplementedError

    @abstractmethod
    def _resolve_char_must_occur_predicate(self, pred):
        raise NotImplementedError

    @abstractmethod
    def _resolve_block_range_lower_bound_predicate(self, pred):
        raise NotImplementedError

    @abstractmethod
    def _resolve_block_range_upper_bound_predicate(self, pred):
        raise NotImplementedError

    def resolve_predicates(self, predicates):
        for pred in predicates:
            if pred.name == 'is_not_parent':
                self._resolve_is_not_parent_predicate(pred)
            elif pred.name == 'block_subtree':
                self._resolve_block_subtree_predicate(pred)
            elif pred.name == 'block_tree':
                self._resolve_block_tree_predicate(pred)
            elif pred.name == 'block_first_tree':
                self._resolve_block_first_tree_predicate(pred)
            elif pred.name == 'char_must_occur':
                self._resolve_char_must_occur_predicate(pred)
            elif pred.name == 'block_range_lower_bound':
                self._resolve_block_range_lower_bound_predicate(pred)
            elif pred.name == 'block_range_upper_bound':
                self._resolve_block_range_upper_bound_predicate(pred)
            else:
                logger.warning('Predicate not handled: {}'.format(pred))

    def next(self):
        if self.z3_solver.check() == z3.sat:
            self.model = {}
            for var in self.variables:
                self.model[var] = int(str(self.z3_solver.model()[self.variables[var]]))
        else:
            self.model = None
        if self.model is not None:
            return self.build_program()
        else:
            logger.debug(f'Enumerator exhausted.')
            return None

    def _block_subtree_rec(self, subtree: ASTNode, program: Node):
        """ Auxiliary function for block_subtree. """
        head_var = self.variables[subtree]
        production_id = program.production.id
        block = [head_var != z3.IntVal(production_id)]
        if len(program.children) == 1:
            assert len(subtree.children) == 2
            children_vars = list(map(lambda x: self.variables[x], subtree.children))
            assert len(children_vars) == 2
            block += self._block_subtree_rec(subtree.children[0], program.children[0])
        elif len(program.children) == 2:
            assert len(subtree.children) == 2
            block += self._block_subtree_rec(subtree.children[0], program.children[0])
            block += self._block_subtree_rec(subtree.children[1], program.children[1])
        return block

    def block_subtree(self, subtree: ASTNode, program: Node):
        """ Block the subtree below the program node from happening in the
        subtree ASTNode. """
        block = self._block_subtree_rec(subtree, program)
        self.z3_solver.add(z3.Or(block))

    @abstractmethod
    def build_program(self):
        raise NotImplementedError

    def __str__(self):
        name = self.__class__.__name__
        if "Enumerator" in name:
            name = name.replace("Enumerator", "")
        if "MultiTree" in name:
            name = name.replace("MultiTree", "MT")
        return name
