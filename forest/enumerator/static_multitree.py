from typing import List

import z3

from forest.spec import TyrellSpec
from .regex_enumerator import RegexEnumerator
from ..dsl import Node, Builder
from ..logger import get_logger

logger = get_logger('forest')


# FIXME: Currently this enumerator requires an "Empty" production to function properly
class StaticMultiTreeEnumerator(RegexEnumerator):

    def __init__(self, main_dsl: TyrellSpec, tree_dsls: List[TyrellSpec], depth):
        super().__init__(main_dsl)
        # self.main_dsl = self.dsl (defined in superclass)
        self.main_dsl = main_dsl
        self.tree_dsls = tree_dsls
        assert len(tree_dsls) > 0
        self.length = len(tree_dsls)
        if depth < 2:
            raise ValueError(f'Depth must be larger or equal to 2: {depth}')
        self.depth = depth

        for i in range(self.length):
            tree = self.build_k_tree(self.max_children, self.depth, i + 1)
            self.trees.append(tree)
            self.nodes.extend(tree.nodes)

        assert len(self.trees) == self.length
        assert len(self.nodes) == (2 ** self.depth - 1) * self.length

        self._create_variables(self.z3_solver)
        self._create_output_constraints(self.z3_solver)
        self._create_leaf_constraints(self.z3_solver)
        self._create_children_constraints(self.z3_solver)
        self._create_union_constraints()
        self.resolve_predicates(self.main_dsl.predicates())

        logger.info(str(self) + f", variables {len(self.variables)}")

    def _create_variables(self, solver):
        """ Create one n-variable per node. """
        for tree in self.trees:
            dsl = self.tree_dsls[tree.id - 1]
            for node in tree.nodes:
                v = z3.Int(self._get_n_var_name(node))
                self.variables[node] = v
                solver.add(z3.And(v >= 0, v < dsl.num_productions()))

        assert len(self.variables) == len(self.nodes)

    def _create_output_constraints(self, solver):
        """ The output production matches the output type """
        # the head of each tree must be a regex
        assert all(
            map(lambda d: d.output == self.tree_dsls[0].output, self.tree_dsls))
        for tree in self.trees:
            head_var = self.variables[tree.head]
            dsl = self.tree_dsls[tree.id - 1]
            output_productions = dsl.get_productions_with_lhs(dsl.output)
            big_or = list(map(lambda p: head_var == p.id, output_productions))
            solver.add(z3.Or(big_or))

    def _create_leaf_constraints(self, solver):
        """ Leaf productions correspond to leaf nodes """
        for tree in self.trees:
            leaf_productions = []
            dsl = self.tree_dsls[tree.id - 1]
            for p in dsl.productions():
                if (not p.is_function()) or str(p).find('Empty') != -1:
                    leaf_productions.append(p)

            for node in tree.nodes:
                if node.children is None:
                    big_or = list(
                        map(lambda l: self.variables[node] == l.id, leaf_productions))
                    solver.add(z3.Or(big_or))

    def _create_children_constraints(self, solver):
        """ Children have the correct type according to parent's
        specification """
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
                                big_or.append(self.variables[parent.children[
                                    child_idx]] == ty.id)
                                big_or.append(self.variables[parent] != prod.id)
                                pass
                            solver.add(z3.Or(big_or))

    def _create_union_constraints(self):
        """ Prevent union of twice the same subtree: (A|A) """
        for tree in self.trees:
            dsl = self.tree_dsls[tree.id - 1]
            for node in tree.nodes:
                if not node.has_children():
                    continue
                test2 = node.children[0].children is None or len(
                    node.children[0].children) == 0
                test3 = node.children[1].children is None or len(
                    node.children[1].children) == 0
                if test2 or test3: continue

                node_var = self.variables[node]
                if dsl.get_function_production("union") is None: return
                union_id = dsl.get_function_production("union").id
                node_is_union = node_var == z3.IntVal(union_id)

                subtree0, subtree1 = node.children[0].get_subtree(), \
                                     node.children[1].get_subtree()
                big_or = []
                for i in range(len(subtree0)):
                    var_i0 = self.variables[subtree0[i]]
                    var_i1 = self.variables[subtree1[i]]
                    big_or.append(var_i0 != var_i1)

                self.z3_solver.add(z3.Implies(node_is_union, z3.Or(big_or)))

    def _resolve_is_not_parent_predicate(self, pred):
        self._check_arg_types(pred, [str, str])

        for tree in self.trees:
            dsl = self.tree_dsls[tree.id - 1]

            parent = dsl.get_function_production(pred.args[0])
            if parent is None:
                continue
            child = dsl.get_function_production(pred.args[1])
            if child is None:
                continue
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
        self.tree_dsls[tree_idx].add_predicate(pred.name, pred.args)

        # We want to run block_subtree only for nodes in the tree in which the program
        # originally occurred.
        for node in self.nodes_until_depth(self.depth - program.depth() + 1,
                                           tree_idx):
            self.block_subtree(node, program)

    def _resolve_block_tree_predicate(self, pred):
        self._check_arg_types(pred, [Node, int])
        program = pred.args[0]
        tree_idx = pred.args[1]
        self.tree_dsls[tree_idx].add_predicate(pred.name, pred.args)

        if self.depth < program.depth():
            return

        self.block_subtree(self.trees[tree_idx].head, program)

    def _resolve_block_first_tree_predicate(self, pred):
        self._check_arg_types(pred, [Node, int])
        program = pred.args[0]
        tree_idx = pred.args[1]
        self.tree_dsls[0].add_predicate(pred.name, pred.args)

        if self.depth < program.depth():
            return
        node = self.trees[0].head
        self.block_subtree(node, program)

    def _resolve_char_must_occur_predicate(self, pred):
        self._check_arg_types(pred, [Node, int])
        program = pred.args[0]
        tree_idx = pred.args[1]
        self.tree_dsls[tree_idx].add_predicate(pred.name, pred.args)

        big_or = []
        for node in self.nodes_until_depth(self.depth - program.depth() + 1,
                                           tree_idx):
            big_or.append(
                self.variables[node] == z3.IntVal(program.production.id))

        self.z3_solver.add(z3.Or(big_or))

    def _resolve_block_range_lower_bound_predicate(self, pred):
        self._check_arg_types(pred, [Node, int])
        program = pred.args[0]
        tree_idx = pred.args[1]
        self.tree_dsls[tree_idx].add_predicate(pred.name, pred.args)

        # block all programs
        bounds = program.args[1].data.split(',')
        assert len(bounds) == 2
        lower_bound = bounds[0]

        # get all children nodes to block:
        ranges_to_block = self.range_lower_bounds[lower_bound]

        for range_node in ranges_to_block:
            program_to_block = program
            program_to_block.args[1] = range_node
            # We want to run block_subtree only for nodes in the tree in which
            # the program originally occurred.
            for node in self.nodes_until_depth(
                    self.depth - program_to_block.depth() + 1, tree_idx):
                self.block_subtree(node, program_to_block)

    def _resolve_block_range_upper_bound_predicate(self, pred):
        self._check_arg_types(pred, [Node, int])
        program = pred.args[0]
        tree_idx = pred.args[1]
        self.tree_dsls[tree_idx].add_predicate(pred.name, pred.args)

        # block all programs

        bounds = program.args[1].data.split(',')
        assert len(bounds) == 2
        upper_bound = bounds[1]

        # get all children nodes to block:
        ranges_to_block = self.range_upper_bounds[upper_bound]

        for range_node in ranges_to_block:
            program_to_block = program
            program_to_block.args[1] = range_node
            # We want to run block_subtree only for nodes in the tree in which
            # the program originally occurred.
            for node in self.nodes_until_depth(
                    self.depth - program_to_block.depth() + 1, tree_idx):
                self.block_subtree(node, program_to_block)

    def block_model(self):
        """ Block current model and all others equivalent to it """
        # block the model using only the variables that correspond to productions
        to_block = list(
            map(lambda x: self.variables[x] != self.model[x], self.variables.keys()))
        self.z3_solver.add(z3.Or(to_block))

        # Find out if some commutative operation was used.
        # FIXME: union is hardcoded as commutative operation!
        if self.main_dsl.get_function_production("union") is None: return

        # commutative_op_nodes contains the variables of all nodes that have id
        # of a commutative operation (in this case, it is only union)
        commutative_op_nodes = []
        for tree in self.trees:
            dsl = self.tree_dsls[tree.id - 1]
            union = dsl.get_function_production("union")
            if union is None:
                continue
            union_id = union.id
            commutative_op_nodes.extend(filter(
                lambda n: int(str(self.model[n])) == union_id, tree.nodes))

        for x in commutative_op_nodes:
            tree_id, node_id = x.tree_id, x.id
            subtree0, subtree1 = self.trees[tree_id - 1].nodes[node_id - 1] \
                                     .children[0].get_subtree(), \
                                 self.trees[tree_id - 1].nodes[node_id - 1] \
                                     .children[1].get_subtree()

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

            block2 += list(
                map(lambda x: self.variables[x] != self.model[x], unblocked))
            self.z3_solver.add(z3.Or(block2))

    def update(self, predicates=None):
        """
        :param predicates: information about the program. If None, enumerator will block complete model.
        """
        if predicates is not None:
            self.resolve_predicates(predicates)
        self.block_model()

    def build_program(self):
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
                prod = self.tree_dsls[t_idx].get_production_or_raise(
                    result[t_idx][n.id - 1])
                productions[t_idx].append(prod)

        head_nodes = []
        assert len(self.trees) == len(productions)
        for tree_idx, tree in enumerate(self.trees):
            dsl = self.tree_dsls[tree_idx]
            builder = Builder(dsl)
            prod_tree = productions[tree_idx]
            builder_nodes = [None] * len(prod_tree)
            assert len(prod_tree) == len(
                tree.nodes), f"{len(prod_tree)} != {len(tree.nodes)}"
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

        return concat_node

    def nodes_until_depth(self, depth: int, tree_idx):
        """ Return all nodes with depth lower than that in the argument. """
        last_node = 2 ** depth - 1
        ret = filter(lambda n: n.id <= last_node, self.trees[tree_idx].nodes)
        return ret

    @staticmethod
    def _get_n_var_name(node):
        return f'n{node.tree_id}_{node.id}'

    def __str__(self):
        base = super(StaticMultiTreeEnumerator, self).__str__()
        return f'{base}(n={self.length}; d={self.depth})'
