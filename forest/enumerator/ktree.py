import z3

from forest.spec import TyrellSpec
from .regex_enumerator import RegexEnumerator
from .. import dsl as D
from ..dsl import Node
from ..logger import get_logger

logger = get_logger('forest')


class KTreeEnumerator(RegexEnumerator):
    def __init__(self, dsl: TyrellSpec, depth):
        super().__init__(dsl)
        if depth <= 0:
            raise ValueError(f'Depth cannot be non-positive: {depth}')
        self.depth = depth
        self.tree = self.build_k_tree(self.max_children, self.depth, 1)
        self.nodes = self.tree.nodes
        self._create_variables(self.z3_solver)
        self._create_output_constraints(self.z3_solver)
        self._create_leaf_constraints(self.z3_solver)
        self._create_children_constraints(self.z3_solver)
        self._create_union_constraints()
        self.resolve_predicates(self.dsl.predicates())

    def _get_n_var_name(self, node):
        return f'n{node.id}'

    def _create_variables(self, solver):
        """ Create one n-variable per node. """
        for node in self.nodes:
            v = z3.Int(self._get_n_var_name(node))
            self.variables[node] = v
            solver.add(z3.And(v >= 0, v < self.dsl.num_productions()))

    def _create_output_constraints(self, solver):
        """ The output production matches the output type """
        # the head of each tree must be a regex
        head_var = self.variables[self.tree.head]
        big_or = list(map(lambda p: head_var == p.id,
                          self.dsl.get_productions_with_lhs(self.dsl.output)))
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
        program = pred.args[0]

        for node in self.nodes_until_depth(self.depth - program.depth() + 1):
            self.block_subtree(node, program)

    def _resolve_block_tree_predicate(self, pred):
        self._check_arg_types(pred, [Node])
        program = pred.args[0]
        if self.depth < program.depth():
            return
        for tree in self.trees:
            node = tree.head
            self.block_subtree(node, program)

    def _resolve_block_first_tree_predicate(self, pred):
        self._check_arg_types(pred, [Node])
        program = pred.args[0]
        if self.depth < program.depth():
            return
        node = self.trees[0].head
        self.block_subtree(node, program)

    def _resolve_block_predicate(self, pred):
        self._check_arg_types(pred, [Node])
        program = pred.args[0]

        for node in self.nodes_until_depth(self.depth - program.depth() + 1):
            self.block_subtree(node, program)

    def _resolve_char_must_occur_predicate(self, pred):
        self._check_arg_types(pred, [Node, int])
        program = pred.args[0]

        big_or = []
        for node in self.nodes_until_depth(self.depth - program.depth() + 1):
            big_or.append(self.variables[node] == z3.IntVal(program.production.id))

        self.z3_solver.add(z3.Or(big_or))

    def _resolve_block_range_lower_bound_predicate(self, pred):
        self._check_arg_types(pred, [Node, int])
        program = pred.args[0]
        tree_idx = pred.args[1]

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
            for node in self.nodes_until_depth(self.depth - program_to_block.depth() + 1):
                self.block_subtree(node, program_to_block)

    def _resolve_block_range_upper_bound_predicate(self, pred):
        self._check_arg_types(pred, [Node, int])
        program = pred.args[0]
        tree_idx = pred.args[1]

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
            for node in self.nodes_until_depth(self.depth - program_to_block.depth() + 1):
                self.block_subtree(node, program_to_block)

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
            elif pred.name == 'block_range_lower_bound':
                self._resolve_block_range_lower_bound_predicate(pred)
            elif pred.name == 'block_range_upper_bound':
                self._resolve_block_range_upper_bound_predicate(pred)
            else:
                logger.warning('Predicate not handled: {}'.format(pred))

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
            node_id = x.id
            subtree0, subtree1 = self.nodes[node_id - 1].children[0].get_subtree(), \
                                 self.nodes[node_id - 1].children[1].get_subtree()
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
        :param predicates: information about the failed program. If None, enumerator will
        block complete model.
        """
        if predicates is not None:
            self.resolve_predicates(predicates)
            for pred in predicates:
                if pred.name == "block_first_tree" or pred.name == "block_tree":
                    self.block_model()
                else:
                    self.dsl.add_predicate(pred.name, pred.args)
        else:
            self.block_model()

    def build_program(self):
        result = [-1] * len(self.nodes)
        for x in self.model.keys():
            node_id = x.id
            result[node_id - 1] = int(str(self.model[x]))

        # code is a list with the productions
        productions = []
        for n in self.nodes:
            prod = self.dsl.get_production_or_raise(result[n.id - 1])
            productions.append(prod)

        builder = D.Builder(self.dsl)
        builder_nodes = [None] * len(self.nodes)
        for y in range(len(self.nodes) - 1, -1, -1):
            assert y == self.nodes[y].id - 1, f"{y} {self.nodes[y].id}"
            if "Empty" not in str(productions[y]):
                children = []
                if self.nodes[y].has_children():
                    for c in self.nodes[y].children:
                        if "Empty" not in str(productions[c.id - 1]):
                            children.append(builder_nodes[c.id - 1])
                builder_nodes[y] = builder.make_node(productions[y].id, children)

        return builder_nodes[0]

    def nodes_until_depth(self, depth: int):
        """ Return all nodes with depth lower than that in the argument. """
        last_node = 2 ** depth - 1
        return self.nodes[:last_node]

    def __str__(self):
        base = super(KTreeEnumerator, self).__str__()
        return f'{base}(d={self.depth})'
