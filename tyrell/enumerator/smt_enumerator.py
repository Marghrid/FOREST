from collections import deque

import z3

from .ast import AST, ASTNode
from .enumerator import Enumerator
from .. import dsl as D
from ..dsl import Node
from ..logger import get_logger
from ..spec import TyrellSpec

logger = get_logger('tyrell.enumerator.smt')


# FIXME: Currently this enumerator requires an "Empty" production to function properly
class SmtEnumerator(Enumerator):
    # z3 solver
    z3_solver = z3.Solver()
    # z3_solver = z3.SolverFor("QF_FD")
    # productions that are leaf
    leaf_productions = []

    # z3 variables for each production node
    variables = []

    # z3 variables to denote if a node is a function or not
    variables_fun = []

    # map from internal k-tree to nodes of program
    program2tree = {}

    def initLeafProductions(self):
        for p in self.spec.productions():
            # FIXME: improve empty integration
            if (not p.is_function()) or str(p).find('Empty') != -1:
                self.leaf_productions.append(p)

    def createVariables(self, solver):
        for x in range(0, len(self.nodes)):
            name = 'n' + str(x + 1)
            v = z3.Int(name)
            self.variables.append(v)
            # variable range constraints
            solver.add(z3.And(v >= 0, v < self.spec.num_productions()))
            hname = 'h' + str(x + 1)
            h = z3.Int(hname)
            self.variables_fun.append(h)
            # high variables range constraints
            solver.add(z3.And(h >= 0, h <= 1))

    def createOutputConstraints(self, solver):
        '''The output production matches the output type'''
        big_or = list(map(lambda p: self.variables[0] == p.id, self.spec.get_productions_with_lhs(self.spec.output)))
        solver.add(z3.Or(big_or))

    def createLocConstraints(self, solver):
        '''Exactly k functions are used in the program'''
        solver.add(self.loc == z3.Sum(self.variables_fun))

    def createInputConstraints(self, solver):
        '''Each input will appear at least once in the program'''
        input_productions = self.spec.get_param_productions()
        for x in range(0, len(input_productions)):
            big_or = list(map(lambda y: self.variables[y] == input_productions[x].id, range(len(self.nodes))))
            solver.add(z3.Or(big_or))

    def createFunctionConstraints(self, solver):
        '''If a function occurs then set the function variable to 1 and 0 otherwise'''
        for x in range(0, len(self.nodes)):
            for p in self.spec.productions():
                # FIXME: improve empty integration
                if p.is_function() and not 'Empty' in str(p):  # str(p).find('Empty') == -1:
                    ctr = z3.Implies(
                        self.variables[x] == p.id, self.variables_fun[x] == 1)
                else:
                    ctr = z3.Implies(
                        self.variables[x] == p.id, self.variables_fun[x] == 0)
                solver.add(ctr)

    def createLeafConstraints(self, solver):
        """Leaf productions correspond to leaf nodes"""
        for x in range(0, len(self.nodes)):
            node = self.nodes[x]
            if node.children is None:
                big_or = list(map(lambda y: self.variables[x] == self.leaf_productions[y].id,
                                  range(len(self.leaf_productions))))
                solver.add(z3.Or(big_or))

    def createChildrenConstraints(self, solver):
        for parent_id in range(0, len(self.nodes)):
            node = self.nodes[parent_id]
            if node.children is not None:
                # the node has children
                for prod in self.spec.productions():
                    for child_idx in range(0, len(node.children)):
                        child_type = 'Empty'
                        if prod.is_function() and child_idx < len(prod.rhs):
                            child_type = str(prod.rhs[child_idx])
                        big_or = []
                        for t in self.spec.get_productions_with_lhs(child_type):
                            big_or.append(self.variables[node.children[child_idx].id - 1] == t.id)
                            big_or.append(self.variables[parent_id] != prod.id)
                        solver.add(z3.Or(big_or))

    def createUnionConstraints(self, z3_solver):
        """ Prevent union of twice the same subtree: (A|B) """
        for node in self.nodes:
            if not node.has_children(): continue
            test2 = not node.children[0].has_children()
            test3 = not node.children[1].has_children()
            if test2 or test3: continue

            node_var = self.variables[node.id - 1]
            if self.spec.get_function_production("union") is None: return
            union_id = self.spec.get_function_production("union").id
            node_is_union = node_var == z3.IntVal(union_id)

            subtree0, subtree1 = self.get_subtree(node.children[0]), \
                                 self.get_subtree(node.children[1])

            bigOr = []
            for i in range(len(subtree0)):
                var_i0 = self.variables[subtree0[i].id - 1]
                var_i1 = self.variables[subtree1[i].id - 1]
                bigOr.append(var_i0 != var_i1)

            self.z3_solver.add(z3.Implies(node_is_union, z3.Or(bigOr)))

    def maxChildren(self) -> int:
        '''Finds the maximum number of children in the productions'''
        return 2  # max(map(len, [p.rhs for p in self.spec.productions()]))

    def buildKTree(self, children, depth):
        '''Builds a K-tree that will contain the program'''
        nodes = []
        tree = AST()
        root = ASTNode(1, 1)
        nb = 1
        tree.head = root
        d = deque()
        d.append(root)
        nodes.append(root)
        while len(d) != 0:
            current = d.popleft()
            current.children = []
            for x in range(0, children):
                nb += 1
                c = ASTNode(nb, current.depth + 1)
                nodes.append(c)
                current.children.append(c)
                if c.depth < depth:
                    d.append(c)
        return tree, nodes

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
                        self.variables[node.children[p].id - 1] == child.id)

                self.solver.add(
                    Implies(Or(ctr_children), self.variables[node.id - 1] != parent.id))

    def _resolve_block_predicate(self, pred):
        self._check_arg_types(pred, [Node])
        program = pred.args[0]

        for node in self.nodes_until_depth(self.depth - program.depth() + 1):
            self.block_subtree(node, program)

    def resolve_predicates(self, predicates):
        try:
            for pred in predicates:
                if pred.name == 'is_not_parent':
                    self._resolve_is_not_parent_predicate(pred)
                elif pred.name == 'block_subtree':
                    self._resolve_block_predicate(pred)
                elif pred.name == "block_first_tree" or pred.name == "block_tree":
                    pass
                else:
                    logger.warning('Predicate not handled: {}'.format(pred))

        except (KeyError, ValueError) as e:
            msg = 'Failed to resolve predicates. {}'.format(e)
            raise RuntimeError(msg) from None

    def __init__(self, spec: TyrellSpec, depth=None, loc=None):
        super().__init__()
        self.z3_solver = z3.Solver()
        self.leaf_productions = []
        self.variables = []
        self.variables_fun = []
        self.spec = spec
        if depth <= 0:
            raise ValueError(
                'Depth cannot be non-positive: {}'.format(depth))
        self.depth = depth
        if loc <= 0:
            raise ValueError(
                f'LOC cannot be non-positive: {loc}')
        self.loc = loc
        self.max_children = self.maxChildren()
        self.tree, self.nodes = self.buildKTree(self.max_children, self.depth)
        self.model = None
        self.initLeafProductions()
        self.createVariables(self.z3_solver)
        self.createOutputConstraints(self.z3_solver)
        # self.createLocConstraints(self.z3_solver)
        self.createInputConstraints(self.z3_solver)
        self.createFunctionConstraints(self.z3_solver)
        self.createLeafConstraints(self.z3_solver)
        self.createChildrenConstraints(self.z3_solver)
        self.createUnionConstraints(self.z3_solver)
        self.resolve_predicates(self.spec.predicates())

    def get_subtree(self, node: ASTNode):
        if node.children is None or len(node.children) < 2:
            return [node]
        else:
            return [node] + self.get_subtree(node.children[0]) + self.get_subtree(node.children[1])

    def blockModel(self):
        # block the model using only the variables that correspond to productions
        block = list(map(lambda x: x != self.model[x], self.variables))
        self.z3_solver.add(z3.Or(block))

        # Find out if some commutative operation was used.
        #FIXME: union is hardcoded as commutative operation!
        if self.spec.get_function_production("union") is None: return
        union_id = self.spec.get_function_production("union").id
        # commutative_op_nodes contains the variables of all nodes that have id of a commutative operation (in this
        # case, it is only union)
        commutative_op_nodes = filter(lambda x: int(str(self.model[x])) == union_id, self.variables)

        for x in commutative_op_nodes:
            node_id = int(str(x)[1:])  # remove "n"
            subtree0, subtree1 = self.get_subtree(self.nodes[node_id - 1].children[0]), \
                                 self.get_subtree(self.nodes[node_id - 1].children[1])
            # block model with subtrees swapped:

            block2 = []
            unblocked = set(self.variables)
            for i, node in enumerate(subtree0):
                node_x = self.variables[node.id - 1]
                other_node = subtree1[i]
                other_node_x = self.variables[other_node.id - 1]
                block2.append(node_x != self.model[other_node_x])
                unblocked.remove(node_x)

            for i, node in enumerate(subtree1):
                node_x = self.variables[node.id - 1]
                other_node = subtree0[i]
                other_node_x = self.variables[other_node.id - 1]
                block2.append(node_x != self.model[other_node_x])
                unblocked.remove(node_x)

            for x in unblocked:
                block2.append(x != self.model[x])

            self.z3_solver.add(z3.Or(block2))

    def update(self, predicates=None):
        """
        :param predicates: information about the program. If None, enumerator will block complete model.
        """
        if predicates is not None:
            self.resolve_predicates(predicates)
            for pred in predicates:
                if pred.name == "block_first_tree" or pred.name == "block_tree":
                    self.blockModel()
                else:
                    self.spec.add_predicate(pred.name, pred.args)
        else:
            self.blockModel()

    def buildProgram(self):
        result = [0] * len(self.model)
        for x in self.model.keys():
            a = str(x)
            if a[:1] == 'n':
                result[int(a[1:]) - 1] = int(str(self.model[x]))

        # result contains the values of 'n' variables
        program2tree = {}
        # code is a list with the productions
        code = []
        for n in self.nodes:
            prod = self.spec.get_production_or_raise(result[n.id - 1])
            code.append(prod)

        builder = D.Builder(self.spec)
        builder_nodes = [None] * len(self.nodes)
        for y in range(len(self.nodes) - 1, -1, -1):
            if "Empty" not in str(code[self.nodes[y].id - 1]):
                children = []
                if self.nodes[y].has_children():
                    for c in self.nodes[y].children:
                        if "Empty" not in str(code[c.id - 1]):
                            children.append(builder_nodes[c.id - 1])
                n = code[self.nodes[y].id - 1].id
                builder_nodes[y] = builder.make_node(n, children)
                program2tree[builder_nodes[y]] = self.nodes[y]

        return builder_nodes[0]

    def next(self):
        res = self.z3_solver.check()
        if res == z3.sat:
            self.model = {}
            for var in self.variables:
                self.model[var] = self.z3_solver.model()[var]
        else:
            self.model = None
        if self.model is not None:
            return self.buildProgram()
        else:
            logger.info(f'Enumerator exhausted for depth {self.depth}.')
            return None

    def nodes_until_depth(self, depth: int):
        last_node = 2 ** depth - 1
        return self.nodes[:last_node]

    def block_subtree_rec(self, subtree: ASTNode, program: Node):
        head_var = self.variables[subtree.id - 1]
        production_id = program.production.id
        block = [head_var != z3.IntVal(production_id)]
        if not program.has_children(): pass
        elif len(program.children) == 1:
            assert len(subtree.children) == 2
            children_vars = list(map(lambda x: self.variables[x.id - 1], subtree.children))
            assert len(children_vars) == 2
            block += self.block_subtree_rec(subtree.children[0], program.children[0])
            # block += [children_vars[1] != z3.IntVal(self.spec.get_function_production("empty").id)]
        elif len(program.children) == 2:
            assert len(subtree.children) == 2
            block += self.block_subtree_rec(subtree.children[0], program.children[0])
            block += self.block_subtree_rec(subtree.children[1], program.children[1])
        return block

    def block_subtree(self, subtree: ASTNode, program: Node):
        block = self.block_subtree_rec(subtree, program)
        self.z3_solver.add(z3.Or(block))
