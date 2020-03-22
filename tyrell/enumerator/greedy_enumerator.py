from collections import deque
from typing import List

import z3

from .ast import AST, ASTNode
from .enumerator import Enumerator
from ..dsl import Node, Builder
from ..logger import get_logger
from ..spec import TyrellSpec

logger = get_logger('tyrell.enumerator.smt')


# FIXME: Currently this enumerator requires an "Empty" production to function properly
class GreedyEnumerator(Enumerator):
    z3_solver = z3.Solver()

    main_dsl: TyrellSpec
    tree_dsls: List[TyrellSpec]

    # z3 variables for each production node
    variables = {}

    # z3 variables to denote if a node is a function or not
    variables_fun = []

    nodes: List[ASTNode]

    trees: List[AST]

    def __init__(self, main_dsl: TyrellSpec, tree_dsls: List[TyrellSpec], depth):
        super().__init__()
        self.z3_solver = z3.Solver()
        self.variables = {}
        self.variables_fun = []
        self.main_dsl = main_dsl
        self.tree_dsls = tree_dsls

        assert len(tree_dsls) > 0

        self.length = len(tree_dsls)
        if depth < 2:
            raise ValueError(
                f'Depth must be larger or equal to 2: {depth}')
        self.depth = depth

        self.max_children = self.max_children()
        self.trees = []
        self.nodes = []

        for i in range(self.length):
            tree = self.build_k_tree(self.max_children, self.depth, i + 1)
            self.trees.append(tree)
            self.nodes.extend(tree.nodes)

        assert len(self.trees) == self.length
        assert len(self.nodes) == (2 ** self.depth - 1) * self.length

        self.model = None

        self.create_variables(self.z3_solver)
        self.create_output_constraints(self.z3_solver)
        self.create_leaf_constraints(self.z3_solver)
        self.create_children_constraints(self.z3_solver)
        self.create_union_constraints()
        self.resolve_predicates(self.main_dsl.predicates())

        logger.debug(f"New enumerator: depth {self.depth}, length {self.length}, variables {len(self.variables)}")

    def create_variables(self, solver):
        """ Create one n-variable per node. """
        for tree in self.trees:
            dsl = self.tree_dsls[tree.id - 1]
            for node in tree.nodes:
                v = z3.Int(self._get_n_var_name(node))
                self.variables[node] = v
                solver.add(z3.And(v >= 0, v < dsl.num_productions()))

        assert len(self.variables) == len(self.nodes)

    def create_output_constraints(self, solver):
        """ The output production matches the output type """
        # the head of each tree must be a regex
        assert all(map(lambda d: d.output == self.tree_dsls[0].output, self.tree_dsls))
        for tree in self.trees:
            head_var = self.variables[tree.head]
            dsl = self.tree_dsls[tree.id - 1]
            output_productions = dsl.get_productions_with_lhs(dsl.output)
            big_or = list(map(lambda p: head_var == p.id, output_productions))
            solver.add(z3.Or(big_or))

    def create_leaf_constraints(self, solver):
        """ Leaf productions correspond to leaf nodes """

        for tree in self.trees:
            leaf_productions = []
            dsl = self.tree_dsls[tree.id - 1]
            for p in dsl.productions():
                if (not p.is_function()) or str(p).find('Empty') != -1:
                    leaf_productions.append(p)

            for node in tree.nodes:
                if node.children is None:
                    big_or = list(map(lambda l: self.variables[node] == l.id, leaf_productions))
                    solver.add(z3.Or(big_or))

    def create_children_constraints(self, solver):
        for tree in self.trees:
            dsl = self.tree_dsls[tree.id - 1]
            for parent in tree.nodes:
                if parent.has_children():
                    for prod in dsl.productions():
                        for child_idx in range(0, len(parent.children)):
                            child_type = 'Empty'
                            if prod.is_function() and child_idx < len(prod.rhs):
                                child_type = str(prod.rhs[child_idx])
                            big_or = []
                            for ty in dsl.get_productions_with_lhs(child_type):
                                big_or.append(self.variables[parent.children[child_idx]] == ty.id)
                                big_or.append(self.variables[parent] != prod.id)
                                pass
                            solver.add(z3.Or(big_or))

    def create_union_constraints(self):
        """ Prevent union of twice the same subtree: (A|B) """
        for tree in self.trees:
            dsl = self.tree_dsls[tree.id - 1]
            for node in tree.nodes:
                if node.children is None or len(node.children) == 0:
                    continue
                test2 = node.children[0].children is None or len(node.children[0].children) == 0
                test3 = node.children[1].children is None or len(node.children[1].children) == 0
                if test2 or test3: continue

                node_var = self.variables[node]
                if dsl.get_function_production("union") is None: return
                union_id = dsl.get_function_production("union").id
                node_is_union = node_var == z3.IntVal(union_id)

                subtree0, subtree1 = self.get_subtree(node.children[0]), \
                                     self.get_subtree(node.children[1])

                bigOr = []
                for i in range(len(subtree0)):
                    var_i0 = self.variables[subtree0[i]]
                    var_i1 = self.variables[subtree1[i]]
                    bigOr.append(var_i0 != var_i1)

                self.z3_solver.add(z3.Implies(node_is_union, z3.Or(bigOr)))

    def max_children(self) -> int:
        """Finds the maximum number of children in the productions"""
        return max(map(lambda p: len(p.rhs), self.main_dsl.productions()))

    def build_k_tree(self, children, depth, tree_id):
        """Builds a K-tree that will contain the program"""
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

    def _resolve_is_not_parent_predicate(self, pred):
        self._check_arg_types(pred, [str, str])


        for tree in self.trees:
            dsl = self.tree_dsls[tree.id-1]

            parent = dsl.get_function_production_or_raise(pred.args[0])
            child = dsl.get_function_production_or_raise(pred.args[1])
            child_pos = []
            # find positions that type-check between parent and child
            for x in range(0, len(parent.rhs)):
                if child.lhs == parent.rhs[x]:
                    child_pos.append(x)

            for node in tree.nodes:
                # not a leaf node
                if node.children is not None:
                    ctr_children = []
                    for p in range(0, len(child_pos)):
                        ctr_children.append(
                            self.variables[node.children[p]] == child.id)

                    self.z3_solver.add(
                        z3.Implies(z3.Or(ctr_children),
                                   self.variables[node] != parent.id))

    def _resolve_block_subtree_predicate(self, pred):
        self._check_arg_types(pred, [Node, int])
        program = pred.args[0]
        tree_idx = pred.args[1]

        # We want to run block_subtree only for nodes in the tree in which the program originally occurred.
        for node in self.nodes_until_depth(self.depth - program.depth() + 1, tree_idx):
            self.block_subtree(node, program)

    def _resolve_block_tree_predicate(self, pred):
        self._check_arg_types(pred, [Node, int])
        program = pred.args[0]
        tree_idx = pred.args[1]

        if self.depth < program.depth():
            return

        self.block_subtree(self.trees[tree_idx].head, program)

    def _resolve_block_first_tree_predicate(self, pred):
        self._check_arg_types(pred, [Node, int])
        program = pred.args[0]
        tree_idx = pred.args[1]
        if self.depth < program.depth():
            return
        node = self.trees[0].head
        self.block_subtree(node, program)

    def _resolve_char_must_occur_predicate(self, pred):
        self._check_arg_types(pred, [Node, int])
        program = pred.args[0]
        tree_idx = pred.args[1]

        big_or = []
        for node in self.nodes_until_depth(self.depth - program.depth() + 1, tree_idx):
            big_or.append(self.variables[node] == z3.IntVal(program.production.id))

        self.z3_solver.add(z3.Or(big_or))

    def resolve_predicates(self, predicates):
        pass
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
            else:
                logger.warning('Predicate not handled: {}'.format(pred))

    def get_subtree(self, node: ASTNode):
        if not node.has_children():
            return [node]
        else:
            assert len(node.children) == 2
            return [node] + self.get_subtree(node.children[0]) + self.get_subtree(node.children[1])

    def block_model(self):
        # block the model using only the variables that correspond to productions
        block = list(map(lambda x: self.variables[x] != self.model[x], self.variables.keys()))
        self.z3_solver.add(z3.Or(block))

        # Find out if some commutative operation was used.
        # FIXME: union is hardcoded as commutative operation!
        # if self.main_dsl.get_function_production("union") is None: return
        # union_id = self.main_dsl.get_function_production("union").id
        # commutative_op_nodes contains the variables of all nodes that have id of a commutative operation (in this
        # case, it is only union)
        # commutative_op_nodes = filter(lambda x: int(str(self.model[x])) == union_id, self.variables)
        #
        # for x in commutative_op_nodes:
        #     tree_id, node_id = x.tree_id, x.id
        #     subtree0, subtree1 = self.get_subtree(self.trees[tree_id - 1].nodes[node_id - 1].children[0]), \
        #                          self.get_subtree(self.trees[tree_id - 1].nodes[node_id - 1].children[1])
        #     # block model with subtrees swapped:
        #
        #     block2 = []
        #     unblocked = set(self.variables.keys())
        #     for i, node in enumerate(subtree0):
        #         node_x = self.variables[node]
        #         other_node = subtree1[i]
        #         block2.append(node_x != self.model[other_node])
        #         unblocked.remove(node)
        #
        #     for i, node in enumerate(subtree1):
        #         node_x = self.variables[node]
        #         other_node = subtree0[i]
        #         block2.append(node_x != self.model[other_node])
        #         unblocked.remove(node)
        #
        #     block2 += list(map(lambda x: self.variables[x] != self.model[x], unblocked))
        #
        #     self.z3_solver.add(z3.Or(block2))

    def update(self, predicates=None):
        """
        :param predicates: information about the program. If None, enumerator will block complete model.
        """
        if predicates is not None:
            self.resolve_predicates(predicates)
            # for pred in predicates:
            #     self.main_dsl.add_predicate(pred.name, pred.args)
        # else:
        self.block_model()

    def buildProgram(self):
        result = [[] for i in range(len(self.trees))]
        for i in range(len(self.trees)):
            result[i] = [-1] * len(self.trees[i].nodes)
        for x in self.model.keys():
            tree_id, node_id = x.tree_id, x.id
            result[tree_id - 1][node_id - 1] = int(str(self.model[x]))

        # result contains the values of 'n' variables
        productions = [[] for i in range(len(self.trees))]
        for t_idx in range(len(self.trees)):
            tree = self.trees[t_idx]
            for n in tree.nodes:
                prod = self.tree_dsls[t_idx].get_production_or_raise(result[t_idx][n.id - 1])
                productions[t_idx].append(prod)

        head_nodes = []
        assert len(self.trees) == len(productions)
        for tree_idx, tree in enumerate(self.trees):
            dsl = self.tree_dsls[tree_idx]
            builder = Builder(dsl)
            prod_tree = productions[tree_idx]
            builder_nodes = [None] * len(prod_tree)
            assert len(prod_tree) == len(tree.nodes), f"{len(prod_tree)} != {len(tree.nodes)}"
            for y in range(len(prod_tree) - 1, -1, -1):
                if "Empty" not in str(prod_tree[y]):
                    children = []
                    if tree.nodes[y].children is not None:
                        for child in tree.nodes[y].children:
                            if "Empty" not in str(prod_tree[child.id - 1]):
                                children.append(builder_nodes[child.id - 1])
                    builder_nodes[y] = builder.make_node(prod_tree[y].id, children)
            head_nodes.append(builder_nodes[0])

        builder = Builder(self.main_dsl)

        concat_prod = self.main_dsl.get_function_production("concat")
        concat_node = builder.make_node(concat_prod, head_nodes)

        param0_prod = self.main_dsl.get_param_production(0)
        param0_node = builder.make_node(param0_prod, [])

        match_prod = self.main_dsl.get_function_production("match")
        match_node = builder.make_node(match_prod, [concat_node, param0_node])

        return match_node

    def next(self):
        res = self.z3_solver.check()
        if res == z3.sat:
            self.model = {}
            for var in self.variables:
                self.model[var] = int(str(self.z3_solver.model()[self.variables[var]]))
        else:
            self.model = None
        if self.model is not None:
            return self.buildProgram()
        else:
            logger.debug(f'Enumerator exhausted for depth {self.depth} and length {self.length}.')
            return None

    def nodes_until_depth(self, depth: int, tree_idx):
        last_node = 2 ** depth - 1
        ret = filter(lambda n: n.id <= last_node, self.trees[tree_idx].nodes)
        return ret

    def block_subtree_rec(self, subtree: ASTNode, program: Node):
        head_var = self.variables[subtree]
        production_id = program.production.id
        block = [head_var != z3.IntVal(production_id)]
        if len(program.children) == 1:
            assert len(subtree.children) == 2
            children_vars = list(map(lambda x: self.variables[x], subtree.children))
            assert len(children_vars) == 2
            block += self.block_subtree_rec(subtree.children[0], program.children[0])
        elif len(program.children) == 2:
            assert len(subtree.children) == 2
            block += self.block_subtree_rec(subtree.children[0], program.children[0])
            block += self.block_subtree_rec(subtree.children[1], program.children[1])
        return block

    def block_subtree(self, subtree: ASTNode, program: Node):
        block = self.block_subtree_rec(subtree, program)
        self.z3_solver.add(z3.Or(block))

    def _get_n_var_name(self, node):
        return f'n{node.tree_id}_{node.id}'
