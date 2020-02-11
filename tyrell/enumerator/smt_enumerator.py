from collections import deque

import z3

from .enumerator import Enumerator
from .optimizer import Optimizer
from .. import dsl as D
from ..logger import get_logger
from ..spec import TyrellSpec

logger = get_logger('tyrell.enumerator.smt')

class AST:
    def __init__(self):
        self.head = None


class ASTNode:
    def __init__(self, nb=None, depth=None, children=None):
        self.id = nb
        self.depth = depth
        self.children = children
        self.production = None

# FIXME: Currently this enumerator requires an "Empty" production to function properly
class SmtEnumerator(Enumerator):
    # z3 solver
    # z3_solver = z3.Solver()
    z3_solver = z3.SolverFor("QF_FD")
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
        ctr = None
        for p in self.spec.get_productions_with_lhs(self.spec.output):
            if ctr is None:
                # variables[0] is the root of the tree
                ctr = self.variables[0] == p.id
            else:
                ctr = z3.Or(ctr, self.variables[0] == p.id)
        solver.add(ctr)

    def createLocConstraints(self, solver):
        '''Exactly k functions are used in the program'''
        ctr = self.variables_fun[0]
        for x in range(1, len(self.variables_fun)):
            ctr += self.variables_fun[x]
        ctr_fun = ctr == self.loc
        solver.add(ctr_fun)

    def createInputConstraints(self, solver):
        '''Each input will appear at least once in the program'''
        input_productions = self.spec.get_param_productions()
        for x in range(0, len(input_productions)):
            ctr = self.variables[0] == input_productions[x].id
            for y in range(1, len(self.nodes)):
                ctr = z3.Or(self.variables[y] == input_productions[x].id, ctr)
            solver.add(ctr)

    def createFunctionConstraints(self, solver):
        '''If a function occurs then set the function variable to 1 and 0 otherwise'''
        assert len(self.nodes) == len(self.variables_fun)
        for x in range(0, len(self.nodes)):
            for p in self.spec.productions():
                # FIXME: improve empty integration
                if p.is_function() and str(p).find('Empty') == -1:
                    ctr = z3.Implies(
                        self.variables[x] == p.id, self.variables_fun[x] == 1)
                    solver.add(ctr)
                else:
                    ctr = z3.Implies(
                        self.variables[x] == p.id, self.variables_fun[x] == 0)
                    solver.add(ctr)

    def createLeafConstraints(self, solver):
        '''Leaf productions correspond to leaf nodes'''
        for x in range(0, len(self.nodes)):
            node = self.nodes[x]
            if node.children is None:
                ctr = self.variables[x] == self.leaf_productions[0].id
                for y in range(1, len(self.leaf_productions)):
                    ctr = z3.Or(self.variables[x] ==
                                self.leaf_productions[y].id, ctr)
                solver.add(ctr)

    def createChildrenConstraints(self, solver):
        for x in range(0, len(self.nodes)):
            node = self.nodes[x]
            if node.children is not None:
                # the node has children
                for p in self.spec.productions():
                    assert len(node.children) > 0
                    for y in range(0, len(node.children)):
                        ctr = None
                        child_type = 'Empty'
                        if p.is_function() and y < len(p.rhs):
                            child_type = str(p.rhs[y])
                        for t in self.spec.get_productions_with_lhs(child_type):
                            if ctr is None:
                                ctr = self.variables[node.children[y].id - 1] == t.id
                            else:
                                ctr = z3.Or(
                                    ctr, self.variables[node.children[y].id - 1] == t.id)
                            ctr = z3.Implies(self.variables[x] == p.id, ctr)
                        solver.add(ctr)

    def maxChildren(self) -> int:
        '''Finds the maximum number of children in the productions'''
        return max(map(len, [p.rhs for p in self.spec.productions()]))

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

    def _resolve_occurs_predicate(self, pred):
        self._check_arg_types(pred, [str, (int, float)])
        prod = self.spec.get_function_production_or_raise(pred.args[0])
        weight = pred.args[1]
        self.optimizer.mk_occurs(prod, weight)

    def _resolve_not_occurs_predicate(self, pred):
        self._check_arg_types(pred, [str, (int, float)])
        prod = self.spec.get_function_production_or_raise(pred.args[0])
        weight = pred.args[1]
        self.optimizer.mk_not_occurs(prod, weight)

    def _resolve_is_not_parent_predicate(self, pred):
        self._check_arg_types(pred, [str, str, (int, float)])
        prod0 = self.spec.get_function_production_or_raise(pred.args[0])
        prod1 = self.spec.get_function_production_or_raise(pred.args[1])
        weight = pred.args[2]
        self.optimizer.mk_is_not_parent(prod0, prod1, weight)

    def _resolve_is_parent_predicate(self, pred):
        self._check_arg_types(pred, [str, str, (int, float)])
        prod0 = self.spec.get_function_production_or_raise(pred.args[0])
        prod1 = self.spec.get_function_production_or_raise(pred.args[1])
        weight = pred.args[2]
        self.optimizer.mk_is_parent(prod0, prod1, weight)

    def _resolve_do_not_concat_predicate(self, pred):
        self._check_arg_types(pred, [str, str])
        # idea: node_is_concat -> child[0] is not args[0] \/ child[0] is not args[1]
        for node in self.nodes:
            test1 = node.children is None or len(node.children) == 0
            if test1: continue
            test2 = node.children[0].children is None or len(node.children[0].children) == 0
            test3 = node.children[1].children is None or len(node.children[1].children) == 0
            if test2 or test3: continue

            node_var = self.variables[node.id-1]
            concat_id = self.spec.get_function_production("concat").id
            node_is_concat = node_var == z3.IntVal(concat_id)

            assert len(node.children) == 2
            child0_var = self.variables[node.children[0].id-1]
            child1_var = self.variables[node.children[1].id-1]
            re_id = self.spec.get_function_production("re").id
            child0_is_re = child0_var == z3.IntVal(re_id)
            child1_is_re = child1_var == z3.IntVal(re_id)

            char_type = self.spec.get_type("Char")
            args0_id = self.spec.get_enum_production(char_type, pred.args[0]).id
            args1_id = self.spec.get_enum_production(char_type, pred.args[1]).id

            child0_child_var = self.variables[node.children[0].children[0].id-1]
            child1_child_var = self.variables[node.children[1].children[0].id-1]

            child0_child_is_args0 = child0_child_var == z3.IntVal(args0_id)
            child1_child_is_args1 = child1_child_var == z3.IntVal(args1_id)

            left_side = z3.And([node_is_concat, child0_is_re, child1_is_re])
            right_side = z3.Not(z3.And(child0_child_is_args0, child1_child_is_args1))

            self.z3_solver.add(z3.Implies(left_side, right_side))

    def _resolve_do_not_kleene_predicate(self, pred):
        self._check_arg_types(pred, [str])
        # idea: node_is_kleene -> child[0] is not args[0]
        for node in self.nodes:
            test1 = node.children is None or len(node.children) == 0
            if test1: continue
            test2 = node.children[0].children is None or len(node.children[0].children) == 0
            if test2: continue

            node_var = self.variables[node.id - 1]
            kleene_id = self.spec.get_function_production("kleene").id
            node_is_kleene = node_var == z3.IntVal(kleene_id)

            assert len(node.children) > 1
            child0_var = self.variables[node.children[0].id - 1]
            re_id = self.spec.get_function_production("re").id
            child0_is_re = child0_var == z3.IntVal(re_id)

            char_type = self.spec.get_type("Char")
            args0_id = self.spec.get_enum_production(char_type, pred.args[0]).id

            child0_child_var = self.variables[node.children[0].children[0].id - 1]

            child0_child_is_args0 = child0_child_var == z3.IntVal(args0_id)

            left_side = z3.And(node_is_kleene, child0_is_re)
            right_side = z3.Not(child0_child_is_args0)

            self.z3_solver.add(z3.Implies(left_side, right_side))

    def _resolve_do_not_posit_predicate(self, pred):
        self._check_arg_types(pred, [str])
        # idea: node_is_posit -> child[0] is not args[0]
        for node in self.nodes:
            test1 = node.children is None or len(node.children) == 0
            if test1: continue
            test2 = node.children[0].children is None or len(node.children[0].children) == 0
            if test2: continue

            node_var = self.variables[node.id - 1]
            posit_id = self.spec.get_function_production("posit").id
            node_is_posit = node_var == z3.IntVal(posit_id)

            assert len(node.children) > 1
            child0_var = self.variables[node.children[0].id - 1]
            re_id = self.spec.get_function_production("re").id
            child0_is_re = child0_var == z3.IntVal(re_id)

            char_type = self.spec.get_type("Char")
            args0_id = self.spec.get_enum_production(char_type, pred.args[0]).id

            child0_child_var = self.variables[node.children[0].children[0].id - 1]

            child0_child_is_args0 = child0_child_var == z3.IntVal(args0_id)

            left_side = z3.And(node_is_posit, child0_is_re)
            right_side = z3.Not(child0_child_is_args0)

            self.z3_solver.add(z3.Implies(left_side, right_side))

    def resolve_predicates(self, predicates):
        try:
            for pred in predicates:
                if pred.name == 'is_not_parent':
                    self._resolve_is_not_parent_predicate(pred)
                elif pred.name == 'do_not_concat':
                    self._resolve_do_not_concat_predicate(pred)
                elif pred.name == 'do_not_kleene':
                    self._resolve_do_not_kleene_predicate(pred)
                elif pred.name == 'do_not_posit':
                    self._resolve_do_not_posit_predicate(pred)
                elif pred.name == 'occurs':
                    self._resolve_occurs_predicate(pred)
                elif pred.name == 'is_parent':
                    self._resolve_is_parent_predicate(pred)
                elif pred.name == 'not_occurs':
                    self._resolve_not_occurs_predicate(pred)

                else:
                    logger.warning('Predicate not handled: {}'.format(pred))
        except (KeyError, ValueError) as e:
            msg = 'Failed to resolve predicates. {}'.format(e)
            raise RuntimeError(msg) from None

    def __init__(self, spec: TyrellSpec, depth=None, loc=None):
        self.z3_solver = z3.Solver()
        self.leaf_productions = []
        self.variables = []
        self.variables_fun = []
        self.program2tree = {}
        self.spec = spec
        if depth <= 0:
            raise ValueError(
                'Depth cannot be non-positive: {}'.format(depth))
        self.depth = depth
        if loc <= 0:
            raise ValueError(
                'LOC cannot be non-positive: {}'.format(loc))
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
        self.optimizer = Optimizer(
            self.z3_solver, spec, self.variables, self.nodes)
        self.resolve_predicates(self.spec.predicates())

    def blockModel(self):
        assert (self.model is not None)
        # m = self.z3_solver.model()
        block = []
        # block the model using only the variables that correspond to productions
        for x in self.variables:
            block.append(x != self.model[x])
        ctr = z3.Or(block)
        self.z3_solver.add(ctr)

        # TODO: block also equivalent models
        # TODO: commutative functions that can have its args swapped
        # TODO: check concatenations and unions

    def update(self, predicates = None):
        if predicates is not None:
            self.resolve_predicates(predicates)
            for pred in predicates:
                self.spec.add_predicate(pred.name, pred.args)
        else:
            self.blockModel()

    def buildProgram(self):
        result = [0] * len(self.model)
        for x in self.model:
            c = x()
            a = str(x)
            if a[:1] == 'n':
                result[int(a[1:]) - 1] = int(str(self.model[c]))

        # result contains the values of 'n' variables
        self.program2tree.clear()
        code = []
        for n in self.nodes:
            prod = self.spec.get_production_or_raise(result[n.id - 1])
            code.append(prod)

        builder = D.Builder(self.spec)
        builder_nodes = [None] * len(self.nodes)
        for y in range(len(self.nodes) - 1, -1, -1):
            # y = len(self.nodes) - x - 1
            if "Empty" not in str(code[self.nodes[y].id - 1]):
                children = []
                if self.nodes[y].children is not None:
                    for c in self.nodes[y].children:
                        if "Empty" not in str(code[c.id - 1]):
                            assert builder_nodes[c.id - 1] is not None
                            children.append(builder_nodes[c.id - 1])
                n = code[self.nodes[y].id - 1].id
                builder_nodes[y] = builder.make_node(n, children)
                self.program2tree[builder_nodes[y]] = self.nodes[y]

        assert (builder_nodes[0] is not None)
        return builder_nodes[0]

    def next(self):
        # self.model = self.optimizer.optimize(self.z3_solver)
        res = self.z3_solver.check()
        if res == z3.sat:
            self.model = self.z3_solver.model()
        else:
            self.model = None
        if self.model is not None:
            return self.buildProgram()
        else:
            return None
