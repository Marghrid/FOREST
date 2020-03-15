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
class FunnyEnumerator(Enumerator):
    z3_solver = z3.Solver()

    # productions that are leaf
    leaf_productions = []

    # z3 variables for each production node
    variables = {}

    # z3 variables to denote if a node is a function or not
    variables_fun = []

    nodes: List[ASTNode]

    trees: List[AST]

    def __init__(self, spec: TyrellSpec, depth=None, length=None):
        super().__init__()
        self.z3_solver = z3.Solver()
        self.leaf_productions = []
        self.variables = {}
        self.variables_fun = []
        self.spec = spec
        if depth <= 0:
            raise ValueError(
                'Depth cannot be non-positive: {}'.format(depth))
        self.depth = depth
        if length <= 0:
            raise ValueError(
                f'LOC cannot be non-positive: {length}')
        self.length = length

        self.max_children = self.maxChildren()
        self.trees = []
        self.nodes = []

        for i in range(self.length):
            tree = self.buildKTree(self.max_children, self.depth, i+1)
            self.trees.append(tree)
            self.nodes.extend(tree.nodes)

        self.model = None
        self.initLeafProductions()
        self.createVariables(self.z3_solver)
        self.createOutputConstraints(self.z3_solver)
        self.createLeafConstraints(self.z3_solver)
        self.createChildrenConstraints(self.z3_solver)
        self.createUnionConstraints(self.z3_solver)
        self.resolve_predicates(self.spec.predicates())


    def initLeafProductions(self):
        for p in self.spec.productions():
            if (not p.is_function()) or str(p).find('Empty') != -1:
                self.leaf_productions.append(p)

    def createVariables(self, solver):
        """ Create one n-variable per node. """
        for node in self.nodes:
            v = z3.Int(self.get_n_var_name(node))
            self.variables[node] = v
            solver.add(z3.And(v >= 0, v < self.spec.num_productions()))

    def createOutputConstraints(self, solver):
        """The output production matches the output type"""
        # the head of each tree must be a regex
        for tree in self.trees:
            head_var = self.variables[tree.head]
            big_or = list(map(lambda p: head_var == p.id, self.spec.get_productions_with_lhs("Regex")))
            solver.add(z3.Or(big_or))

    def createLeafConstraints(self, solver):
        """Leaf productions correspond to leaf nodes"""
        for node in self.nodes:
            if node.children is None:
                big_or = list(map(lambda y: self.variables[node] == self.leaf_productions[y].id,
                                  range(len(self.leaf_productions))))
                solver.add(z3.Or(big_or))

    def createChildrenConstraints(self, solver):
            for parent in self.nodes:
                if parent.children is not None:
                    # the node has children
                    for prod in self.spec.productions():
                        for child_idx in range(0, len(parent.children)):
                            child_type = 'Empty'
                            if prod.is_function() and child_idx < len(prod.rhs):
                                child_type = str(prod.rhs[child_idx])
                            big_or = []
                            for ty in self.spec.get_productions_with_lhs(child_type):
                                big_or.append(self.variables[parent.children[child_idx]] == ty.id)
                                big_or.append(self.variables[parent] != prod.id)
                                pass
                            solver.add(z3.Or(big_or))

    def createUnionConstraints(self, z3_solver):
        """ Prevent union of twice the same subtree: (A|B) """
        for node in self.nodes:
                if node.children is None or len(node.children) == 0: continue
                test2 = node.children[0].children is None or len(node.children[0].children) == 0
                test3 = node.children[1].children is None or len(node.children[1].children) == 0
                if test2 or test3: continue

                node_var = self.variables[node]
                if self.spec.get_function_production("union") is None: return
                union_id = self.spec.get_function_production("union").id
                node_is_union = node_var == z3.IntVal(union_id)

                subtree0, subtree1 = self.get_subtree(node.children[0]), \
                                     self.get_subtree(node.children[1])

                bigOr = []
                for i in range(len(subtree0)):
                    var_i0 = self.variables[subtree0[i]]
                    var_i1 = self.variables[subtree1[i]]
                    bigOr.append(var_i0 != var_i1)

                self.z3_solver.add(z3.Implies(node_is_union, z3.Or(bigOr)))

    def maxChildren(self) -> int:
        '''Finds the maximum number of children in the productions'''
        return 2 # max(map(len, [p.rhs for p in self.spec.productions()]))

    def buildKTree(self, children, depth, id):
        """Builds a K-tree that will contain the program"""
        tree = AST(id)
        root = ASTNode(1, 1, None, id)
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
                c = ASTNode(nb, current.depth + 1, None, id)
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
        parent = self.spec.get_function_production_or_raise(pred.args[0])
        child = self.spec.get_function_production_or_raise(pred.args[1])
        child_pos = []
        # find positions that type-check between parent and child
        for x in range(0, len(parent.rhs)):
            if child.lhs == parent.rhs[x]:
                child_pos.append(x)
        
        for node in self.nodes:
            # not a leaf node
            if node.children != None:
                ctr_children = []
                for p in range(0, len(child_pos)):
                    ctr_children.append(
                        self.variables[node.children[p]] == child.id)

                self.z3_solver.add(
                    z3.Implies(z3.Or(ctr_children),
                               self.variables[node] != parent.id))

    def _resolve_block_predicate(self, pred):
        self._check_arg_types(pred, [Node])
        program = pred.args[0]

        for node in self.nodes_until_depth(self.depth - program.depth() + 1):
            self.block_subtree(node, program)

    def resolve_predicates(self, predicates):
        # try:
            for pred in predicates:
                if pred.name == 'is_not_parent':
                    self._resolve_is_not_parent_predicate(pred)
                elif pred.name == 'do_not_concat':
                    self._resolve_block_predicate(pred)
                elif pred.name == 'do_not_kleene':
                    self._resolve_block_predicate(pred)
                elif pred.name == 'do_not_posit':
                    self._resolve_block_predicate(pred)
                elif pred.name == 'do_not_copies':
                    self._resolve_block_predicate(pred)
                else:
                    logger.warning('Predicate not handled: {}'.format(pred))

    def get_subtree(self, node: ASTNode):
        if node.children is None or len(node.children) < 2:
            return [node]
        else:
            return [node] + self.get_subtree(node.children[0]) + self.get_subtree(node.children[1])

    def blockModel(self):
        # block the model using only the variables that correspond to productions
        block = list(map(lambda x: self.variables[x] != self.model[x], self.variables.keys()))
        self.z3_solver.add(z3.Or(block))

        # Find out if some commutative operation was used.
        # FIXME: union is hardcoded as commutative operation!
        if self.spec.get_function_production("union") is None: return
        union_id = self.spec.get_function_production("union").id
        # commutative_op_nodes contains the variables of all nodes that have id of a commutative operation (in this
        # case, it is only union)
        commutative_op_nodes = filter(lambda x: int(str(self.model[x])) == union_id, self.variables)

        for x in commutative_op_nodes:
            tree_id, node_id = x.tree_id, x.id
            subtree0, subtree1 = self.get_subtree(self.trees[tree_id-1].nodes[node_id - 1].children[0]), \
                                 self.get_subtree(self.trees[tree_id-1].nodes[node_id - 1].children[1])
            # block model with subtrees swapped:

            block2 = []
            unblocked = set(self.variables.keys())
            for i, node in enumerate(subtree0):
                node_x = self.variables[node]
                other_node = subtree1[i]
                block2.append(node_x != self.model[other_node])
                unblocked.remove(node)

            for i, node in enumerate(subtree1):
                node_x = self.variables[node]
                other_node = subtree0[i]
                block2.append(node_x != self.model[other_node])
                unblocked.remove(node)

            block2 += list(map(lambda x: self.variables[x] != self.model[x], unblocked))

            self.z3_solver.add(z3.Or(block2))

    def update(self, predicates=None):
        """
        :param predicates: information about the program. If None, enumerator will block complete model.
        """
        if predicates is not None:
            self.resolve_predicates(predicates)
            for pred in predicates:
                self.spec.add_predicate(pred.name, pred.args)
        # else:
        self.blockModel()

    def buildProgram(self):
        result = [[] for i in range(len(self.trees))]
        for i in range(len(self.trees)):
            result[i] = [-1 for k in range(len(self.trees[i].nodes))]
        for x in self.model.keys():
            tree_id, node_id = x.tree_id, x.id
            result[tree_id-1][node_id-1] = int(str(self.model[x]))

        # result contains the values of 'n' variables
        productions = [[] for i in range(len(self.trees))]
        for t_idx in range(len(self.trees)):
            tree = self.trees[t_idx]
            for n in tree.nodes:
                prod = self.spec.get_production_or_raise(result[t_idx][n.id - 1])
                productions[t_idx].append(prod)

        builder = Builder(self.spec)
        head_nodes = []
        assert len(self.trees) == len(productions)
        for tree_idx, tree in enumerate(self.trees):
            prod_tree = productions[tree_idx]
            builder_nodes = [None] * len(prod_tree)
            assert len(prod_tree) == len(tree.nodes), f"{len(prod_tree)} != {len(tree.nodes)}"
            for y in range(len(prod_tree) - 1, -1, -1):
                # print("production", prod_tree[y])
                if "Empty" not in str(prod_tree[y]):
                    children = []
                    if tree.nodes[y].children is not None:
                        for child in tree.nodes[y].children:
                            if "Empty" not in str(prod_tree[child.id - 1]):
                                children.append(builder_nodes[child.id - 1])
                    builder_nodes[y] = builder.make_node(prod_tree[y].id, children)
            head_nodes.append(builder_nodes[0])

        concat_prod = self.spec.get_function_production("concat")
        concat_node = builder.make_node(concat_prod, head_nodes)

        param0_prod = self.spec.get_param_production(0)
        param0_node = builder.make_node(param0_prod, [])

        match_prod = self.spec.get_function_production("match")
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

    def nodes_until_depth(self, depth: int):
        last_node = 2 ** depth - 1
        ret = []
        for tree in self.trees:
            ret.extend(filter(lambda n: n.id <= last_node, tree.nodes))

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

    def get_n_var_name(self, node):
        return f'n{node.tree_id}_{node.id}'

    def get_ids_from_n_var_name(self, name):
        ids = name.split("_")
        tree_id = int(ids[0][1:]) # remove n
        node_id = int(ids[1])
        return tree_id, node_id
