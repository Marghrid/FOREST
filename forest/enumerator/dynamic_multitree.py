import z3

from forest.spec import TyrellSpec
from .regex_enumerator import RegexEnumerator
from ..dsl import Node, Builder
from ..logger import get_logger

logger = get_logger('forest')


class DynamicMultiTreeEnumerator(RegexEnumerator):

    def __init__(self, dsl: TyrellSpec, depth=None, length=None):
        super().__init__(dsl)
        if depth < 2:
            raise ValueError(f'Depth must be larger or equal to 2: {depth}')
        self.depth = depth
        if length < 1:
            raise ValueError(f'Length must be larger or equal to 1: {length}')
        self.length = length

        for i in range(self.length):
            tree = self.build_k_tree(self.max_children, self.depth, i + 1)
            self.trees.append(tree)
            self.nodes.extend(tree.nodes)

        self._create_variables(self.z3_solver)
        self._create_output_constraints(self.z3_solver)
        self._create_leaf_constraints(self.z3_solver)
        self._create_children_constraints(self.z3_solver)
        self._create_union_constraints()
        self.resolve_predicates(self.dsl.predicates())

        logger.debug(
            f"New enumerator: depth {self.depth}, length {self.length}, variables {len(self.variables)}")

    def _create_variables(self, solver):
        """ Create one n-variable per node. """
        for node in self.nodes:
            v = z3.Int(self._get_n_var_name(node))
            self.variables[node] = v
            solver.add(z3.And(v >= 0, v < self.dsl.num_productions()))

    def _create_output_constraints(self, solver):
        """ The output production matches the output type """
        # the head of each tree must be a regex
        for tree in self.trees:
            head_var = self.variables[tree.head]
            big_or = list(map(lambda p: head_var == p.id,
                              self.dsl.get_productions_with_lhs("Regex")))
            solver.add(z3.Or(big_or))

    def _create_leaf_constraints(self, solver):
        """ Leaf productions correspond to leaf nodes """
        leaf_productions = []
        for p in self.dsl.productions():
            if (not p.is_function()) or str(p).find('Empty') != -1:
                leaf_productions.append(p)
        for node in self.nodes:
            if node.children is None:
                big_or = list(
                    map(lambda lp: self.variables[node] == lp.id, leaf_productions))
                solver.add(z3.Or(big_or))

    def _create_children_constraints(self, solver):
        """ If a DSL symbol p is assigned to a node i, the children of i must have
        types consistent with the parameters of p. """
        for parent in self.nodes:
            if parent.children is not None:
                # the node has children
                for prod in self.dsl.productions():
                    for child_idx in range(0, len(parent.children)):
                        child_type = 'Empty'
                        if prod.is_function() and child_idx < len(prod.rhs):
                            child_type = str(prod.rhs[child_idx])
                        big_or = []
                        for ty in self.dsl.get_productions_with_lhs(child_type):
                            big_or.append(
                                self.variables[parent.children[child_idx]] == ty.id)
                            big_or.append(self.variables[parent] != prod.id)
                            pass
                        solver.add(z3.Or(big_or))

    def _create_union_constraints(self):
        """ Prevent union of twice the same subtree: (A|B) """
        for node in self.nodes:
            if node.children is None or len(node.children) == 0:
                continue
            test2 = node.children[0].children is None or len(
                node.children[0].children) == 0
            test3 = node.children[1].children is None or len(
                node.children[1].children) == 0
            if test2 or test3: continue

            node_var = self.variables[node]
            if self.dsl.get_function_production("union") is None: return
            union_id = self.dsl.get_function_production("union").id
            node_is_union = node_var == z3.IntVal(union_id)

            subtree0, subtree1 = node.children[0].get_subtree(), \
                                 node.children[1].get_subtree()

            bigOr = []
            for i in range(len(subtree0)):
                var_i0 = self.variables[subtree0[i]]
                var_i1 = self.variables[subtree1[i]]
                bigOr.append(var_i0 != var_i1)

            self.z3_solver.add(z3.Implies(node_is_union, z3.Or(bigOr)))

    def _resolve_is_not_parent_predicate(self, pred):
        self._check_arg_types(pred, [str, str])
        parent = self.dsl.get_function_production_or_raise(pred.args[0])
        child = self.dsl.get_function_production_or_raise(pred.args[1])
        child_pos = []
        # find positions that type-check between parent and child
        for x in range(0, len(parent.rhs)):
            if child.lhs == parent.rhs[x]:
                child_pos.append(x)

        for node in self.nodes:
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
        self._check_arg_types(pred, [Node])
        regex = pred.args[0]

        for node in self.nodes_until_depth(self.depth - regex.depth() + 1):
            self.block_subtree(node, regex)

    def _resolve_block_tree_predicate(self, pred):
        self._check_arg_types(pred, [Node])
        regex = pred.args[0]

        if self.depth < regex.depth():
            return
        for tree in self.trees:
            node = tree.head
            self.block_subtree(node, regex)

    def _resolve_block_first_tree_predicate(self, pred):
        self._check_arg_types(pred, [Node])
        regex = pred.args[0]
        if self.depth < regex.depth():
            return
        node = self.trees[0].head
        self.block_subtree(node, regex)

    def _resolve_char_must_occur_predicate(self, pred):
        self._check_arg_types(pred, [Node])
        regex = pred.args[0]

        big_or = []
        for node in self.nodes_until_depth(self.depth - regex.depth() + 1):
            big_or.append(self.variables[node] == z3.IntVal(regex.production.id))

        self.z3_solver.add(z3.Or(big_or))

    def _resolve_block_range_lower_bound_predicate(self, pred):
        self._check_arg_types(pred, [Node, int])
        regex = pred.args[0]
        tree_idx = pred.args[1]

        bounds = regex.args[1].data.split(',')
        assert len(bounds) == 2
        lower_bound = bounds[0]

        # get all children nodes to block:
        ranges_to_block = self.range_lower_bounds[lower_bound]

        for range_node in ranges_to_block:
            to_block = regex
            to_block.args[1] = range_node
            # We want to run block_subtree only for nodes in the tree in which
            # the regex originally occurred.
            for node in self.nodes_until_depth(self.depth - to_block.depth() + 1):
                self.block_subtree(node, to_block)

    def _resolve_block_range_upper_bound_predicate(self, pred):
        self._check_arg_types(pred, [Node, int])
        regex = pred.args[0]
        tree_idx = pred.args[1]

        bounds = regex.args[1].data.split(',')
        assert len(bounds) == 2
        upper_bound = bounds[1]

        # get all children nodes to block:
        ranges_to_block = self.range_upper_bounds[upper_bound]

        for range_node in ranges_to_block:
            to_block = regex
            to_block.args[1] = range_node
            # We want to run block_subtree only for nodes in the tree in which
            # the regex originally occurred.
            for node in self.nodes_until_depth(self.depth - to_block.depth() + 1):
                self.block_subtree(node, to_block)

    def block_model(self):
        """ Block current model and all others equivalent to it """
        # block the model using only the variables that correspond to productions
        block = list(
            map(lambda x: self.variables[x] != self.model[x], self.variables.keys()))
        self.z3_solver.add(z3.Or(block))

        # Find out if some commutative operation was used.
        # FIXME: union is hardcoded as commutative operation!
        if self.dsl.get_function_production("union") is None: return
        union_id = self.dsl.get_function_production("union").id
        # commutative_op_nodes contains the variables of all nodes that have id of a
        # commutative operation (in this case, it is only union)
        commutative_op_nodes = filter(lambda x: int(str(self.model[x])) == union_id,
                                      self.variables)

        for x in commutative_op_nodes:
            tree_id, node_id = x.tree_id, x.id
            subt0 = self.trees[tree_id - 1].nodes[node_id - 1].children[0].get_subtree()
            subt1 = self.trees[tree_id - 1].nodes[node_id - 1].children[1].get_subtree()
            # block model with subtrees swapped:
            block2 = []
            unblocked = set(self.variables.keys())
            for i, node in enumerate(subt0):
                node_x = self.variables[node]
                other_node = subt1[i]
                block2.append(node_x != self.model[other_node])
                unblocked.remove(node)

            for i, node in enumerate(subt1):
                node_x = self.variables[node]
                other_node = subt0[i]
                block2.append(node_x != self.model[other_node])
                unblocked.remove(node)

            block2 += list(map(lambda x: self.variables[x] != self.model[x], unblocked))

            self.z3_solver.add(z3.Or(block2))

    def update(self, predicates=None):
        """
        :param predicates: information about the program. If None, enumerator will
        block complete model.
        """
        if predicates is not None:
            self.resolve_predicates(predicates)
            for pred in predicates:
                self.dsl.add_predicate(pred.name, pred.args)
        # else:
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
                prod = self.dsl.get_production_or_raise(result[t_idx][n.id - 1])
                productions[t_idx].append(prod)

        builder = Builder(self.dsl)
        head_nodes = []
        assert len(self.trees) == len(productions)
        for tree_idx, tree in enumerate(self.trees):
            prod_tree = productions[tree_idx]
            builder_nodes = [None] * len(prod_tree)
            assert len(prod_tree) == len(tree.nodes)
            for y in range(len(prod_tree) - 1, -1, -1):
                if "Empty" not in str(prod_tree[y]):
                    children = []
                    if tree.nodes[y].children is not None:
                        for child in tree.nodes[y].children:
                            if "Empty" not in str(prod_tree[child.id - 1]):
                                children.append(builder_nodes[child.id - 1])
                    builder_nodes[y] = builder.make_node(prod_tree[y].id, children)
            head_nodes.append(builder_nodes[0])

        concat_prod = self.dsl.get_function_production("concat")
        concat_node = builder.make_node(concat_prod, head_nodes)

        return concat_node

    def nodes_until_depth(self, depth: int):
        """ Return all nodes with depth lower than that in the argument. """
        last_node = 2 ** depth - 1
        ret = []
        for tree in self.trees:
            ret.extend(filter(lambda n: n.id <= last_node, tree.nodes))

        return ret

    def _get_n_var_name(self, node):
        return f'n{node.tree_id}_{node.id}'

    def __str__(self):
        base = super(DynamicMultiTreeEnumerator, self).__str__()
        return f'{base}(n={self.length}; d={self.depth})'
