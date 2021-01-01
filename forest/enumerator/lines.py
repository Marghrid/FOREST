# File lines.py imported to this project from SQUARES
# (https://github.com/squares-sql/SQUARES)

import time
from collections import defaultdict
from copy import deepcopy
from logging import getLogger

import z3

from forest.spec import TyrellSpec
from .regex_enumerator import RegexEnumerator
from .. import dsl as D

logger = getLogger('forest.enumerator.smt')


class Node(object):
    def __init__(self, nb=None):
        self.nb = nb
        self.var = None
        self.parent = None
        self.children = None
        self.production = None
        self.h = None
        self.id = None

    def __repr__(self) -> str:
        return 'Node({})'.format(self.nb)


class Root(Node):
    def __init__(self, id=None, nb=None, depth=None, children=None, type=None):
        super().__init__(nb)
        self.id = id
        self.depth = depth  # num of children
        self.children = children
        self.type = type

    def __repr__(self) -> str:
        return 'Root({}, children={})'.format(self.id, len(self.children))


class Leaf(Node):
    def __init__(self, nb=None, parent=None, lines=None):
        super().__init__(nb)
        self.parent = parent  # parent id
        self.lines = lines

    def __repr__(self) -> str:
        return 'Leaf({}, parent={})'.format(self.nb, self.parent)


class LineProduction(object):
    def __init__(self, id=None, type=None):
        self.id = id
        self.lhs = type


def write_lattice(node, pos):
    try:
        string = str(pos[node.nb])
    except:
        string = str(node.id)
    for c in node.children:
        string += write_lattice(c, pos)
    return string


class LinesEnumerator(RegexEnumerator):

    def __init__(self, spec: TyrellSpec, loc=None, sym_breaker=False,
                 break_sym_online=False):

        self.z3_solver = z3.Solver()

        self.z3_solver.set('random_seed', 7)
        self.z3_solver.set('sat.random_seed', 7)

        # productions that are leaves
        self.leaf_productions = []

        self.line_productions = []

        # for learning
        self.program2tree = {}

        # z3 variables for each production node
        self.variables = []
        self.spec = spec
        self.num_constraints = 0
        self.num_variables = 0
        self.sym_breaker = sym_breaker
        self.break_sym_online = break_sym_online
        if loc <= 0:
            raise ValueError(f'LOC cannot be non-positive: {loc}')
        self.start_time = time.time()
        self.loc = loc

        self.parentId = dict()
        if self.sym_breaker:
            if self.loc > 2:
                root = Node(1)
                root.h = 1
                id, tree = self.create_clean_tree(1, root)
                tree.insert(0, root)
                self.cleanedTree = tree
                self.symFinder = SymmetryFinder(self.loc)

            self.lattices = dict()
            if self.loc > 2 and not self.break_sym_online:
                self.find_lattices()

        self.cleanedModel = dict()
        self.num_prods = self.spec.num_productions()
        self.max_children = self.max_children()
        self.find_types()
        self.init_leaf_productions()
        self.init_line_productions()
        self.linesVars = []
        self.typeVars = []
        self.line_vars_by_line = defaultdict(list)
        self.roots, self.leafs = self.build_trees()
        self.model = None
        # Times
        self.symTime = 0
        self.totalSymTime = 0
        self.solverTime = 0
        self.blockedModels = 0
        self.totalBlockedModels = 0

        self.modelConstraint = 0
        self.create_output_constraints()
        self.create_lines_constraints()
        self.create_type_constraints()
        self.create_children_constraints()
        self._production_id_cache = defaultdict(set)
        for p in self.spec.productions():
            if p.is_enum():
                self._production_id_cache[p._get_rhs()].add(p.id)
        self.resolve_predicates(self.spec.predicates())
        logger.info('Number of Nodes: {} '.format(len(self.roots + self.leafs)))
        logger.info('Number of Variables: {}'.format(
            len(self.variables + self.typeVars + self.linesVars)))
        logger.info('Number of Constraints: {}'.format(self.num_constraints))
        logger.info('Time spent encoding: {}'.format(time.time() - self.start_time))
        res = self.z3_solver.check()
        if res != z3.sat:
            logger.warning(f"There is no solution for current loc ({self.loc}).")
            return
        self.model = self.z3_solver.model()
        self.get_model_constraint()

    def init_leaf_productions(self):
        for p in self.spec.productions():
            if not p.is_function() or str(p).find('Empty') != -1:
                self.leaf_productions.append(p)

    def init_line_productions(self):
        for l in range(1, self.loc):
            line_productions = []
            for t in self.types:
                self.num_prods += 1
                line_productions.append(
                    LineProduction(self.num_prods, self.spec.get_type(t)))
            self.line_productions.append(line_productions)

    def find_types(self):
        types = []
        for t in self.spec.types():
            types.append(t.name)
            flag = False
            for p in self.spec.productions():
                if not p.is_function() or p.lhs.name == 'Empty':
                    continue
                if p.lhs.name == types[-1]:
                    flag = True
                    break
            if not flag:
                types.pop()
        self.types = types
        self.num_types = len(self.types)

    def build_trees(self):
        """Builds a loc trees, each tree will be a line of the program"""
        nodes = []
        nb = 1
        leafs = []
        for i in range(1, self.loc + 1):
            n = Root(i, nb, self.max_children)
            n.var = self.create_root_variables(nb)
            children = []
            for x in range(self.max_children):
                nb += 1
                child = Leaf(nb, n)
                child.lines = self.create_lines_variables(nb, n.id)
                child.var = self.create_leaf_variables(nb, n.id)
                children.append(child)
                leafs.append(child)
            n.children = children
            n.type = self.create_type_variables(n.id)
            nodes.append(n)
            nb += 1
        return nodes, leafs

    def create_lines_variables(self, nb, parent):
        lines = []
        for x in range(1, parent):
            name = f'l{str(nb)}_{str(x)}'
            var = z3.Int(name)
            self.linesVars.append(var)
            self.line_vars_by_line[x].append(var)
            lines.append(var)
            # variable range constraints
            self.z3_solver.add(z3.Or(var == 0, var == 1))
            self.num_constraints += 1
        return lines

    def create_type_variables(self, nb):
        var = z3.Int(f't{str(nb)}')
        # variable range constraints
        self.typeVars.append(var)
        self.z3_solver.add(z3.And(var >= 0, var < self.num_types))
        self.num_constraints += 1
        return var

    def create_root_variables(self, nb):
        name = f'n{str(nb)}'
        v = z3.Int(name)
        self.variables.append(v)
        ctr = []
        for p in self.spec.productions():
            if p not in self.leaf_productions:
                ctr.append(v == p.id)
        self.z3_solver.add(z3.Or(ctr))
        self.num_constraints += 1
        return v

    def create_leaf_variables(self, nb, parent):
        name = f'n{nb}'
        var = z3.Int(name)
        self.variables.append(var)

        ctr = []
        for p in self.leaf_productions:
            ctr.append(var == p.id)

        for a in range(0, parent - 1):
            for p in self.line_productions[a]:
                ctr.append(var == p.id)

        self.z3_solver.add(z3.Or(ctr))
        self.num_constraints += 1
        self.parentId[nb] = parent
        return var

    def create_output_constraints(self):
        """The output production matches the output type"""
        ctr = []
        var = self.roots[-1].var  # last line corresponds to the output line
        for p in self.spec.get_productions_with_lhs(self.spec.output):
            ctr.append(var == p.id)
        self.z3_solver.add(z3.Or(ctr))
        self.num_constraints += 1

    def create_lines_constraints(self):
        """Each line is used at least once in the program"""
        for r in range(1, len(self.roots)):
            ctr = None
            for line_var in self.line_vars_by_line[r]:
                if ctr is None:
                    ctr = line_var
                else:
                    ctr += line_var

            self.z3_solver.add(ctr >= 1)
            self.num_constraints += 1

    def create_input_constraints(self):
        """Each input will appear at least once in the program"""
        input_productions = self.spec.get_param_productions()
        for prod in input_productions:
            ctr = []
            for y in self.leafs:
                ctr.append(y.var == prod.id)
            self.z3_solver.add(z3.Or(ctr))
            self.num_constraints += 1

    def create_type_constraints(self):
        """If a production is used in a node, then the nodes' type is equal to the production's type"""
        for r in self.roots:
            for t in range(len(self.types)):  # todo one of the fors can be removed
                if self.types[t] == 'Empty':
                    continue
                for p in self.spec.productions():
                    if p.is_function() and p.lhs.name == self.types[t]:
                        self.z3_solver.add(z3.Implies(r.var == p.id, r.type == t))
                        self.num_constraints += 1

    def create_children_constraints(self):
        for r in self.roots:
            for p in self.spec.productions():
                if not p.is_function() or p.lhs.name == 'Empty':
                    continue
                aux = r.var == p.id
                for c in range(len(r.children)):
                    ctr = []
                    if c >= len(p.rhs):
                        self.num_constraints += 1
                        self.z3_solver.add(z3.Implies(aux, r.children[c].var ==
                                                      self.leaf_productions[0].id))
                        continue

                    for leaf_production in self.leaf_productions:
                        if leaf_production.lhs.name == p.rhs[c].name:
                            ctr.append(r.children[c].var == leaf_production.id)

                    for l in range(r.id - 1):
                        for line_production in self.line_productions[l]:
                            if line_production.lhs.name == p.rhs[c].name:
                                ctr.append(r.children[c].var == line_production.id)
                                # if a previous line is used, then its flag must be true
                                line_var = r.children[c].lines[l]
                                self.z3_solver.add(z3.Implies(line_var == 1,
                                                              r.children[c].var == line_production.id))
                                self.z3_solver.add(z3.Implies(r.children[c].var ==
                                                              line_production.id, line_var == 1))
                                self.num_constraints += 2

                    self.num_constraints += 1
                    self.z3_solver.add(z3.Implies(aux, z3.Or(*ctr)))

    def max_children(self) -> int:
        '''Finds the maximum number of children in the productions'''
        max = 0
        for p in self.spec.productions():
            if len(p.rhs) > max:
                max = len(p.rhs)
        return max

    @staticmethod
    def _check_arg_types(pred, python_tys):
        if pred.num_args() < len(python_tys):
            msg = 'Predicate "{}" must have at least {} arugments. Only {} is found.'.format(
                pred.name, len(python_tys), pred.num_args())
            raise ValueError(msg)
        for index, (arg, python_ty) in enumerate(zip(pred.args, python_tys)):
            if not isinstance(arg, python_ty):
                msg = f'Argument {index} of predicate {pred.name} has unexpected type.'
                raise ValueError(msg)

    def _resolve_is_not_parent_predicate(self, pred):
        self._check_arg_types(pred, [str, str])
        prod0 = self.spec.get_function_production_or_raise(pred.args[0])
        prod1 = self.spec.get_function_production_or_raise(pred.args[1])

        for r in self.roots:
            for s in range(len(r.children[0].lines)):
                children = []
                for c in r.children:
                    children.append(c.lines[s] == 1)
                self.z3_solver.add(
                    z3.Implies(z3.And(z3.Or(children), self.roots[s].var == prod1.id),
                               r.var != prod0.id))

    def _resolve_distinct_inputs_predicate(self, pred):
        self._check_arg_types(pred, [str])
        production = self.spec.get_function_production_or_raise(pred.args[0])
        for r in self.roots:
            for c1 in range(len(r.children)):
                child1 = r.children[c1]
                for c2 in range(c1 + 1, len(r.children)):
                    child2 = r.children[c2]
                    # this works because even a inner_join between two filters, the children will have different values for the variables because of the lines produtions
                    self.z3_solver.add(z3.Implies(r.var == production.id,
                                                  z3.Or(child1.var != child2.var,
                                                        z3.And(child1.var == 0,
                                                               child2.var == 0))))

    def _resolve_distinct_filters_predicate(self, pred):
        self._check_arg_types(pred, [str])
        prod0 = self.spec.get_function_production_or_raise(pred.args[0])
        for r in self.roots:
            self.z3_solver.add(z3.Implies(r.var == prod0.id,
                                          r.children[int(pred.args[1])].var != r.children[
                                              int(pred.args[2])].var))

    def _resolve_constant_occurs_predicate(self, pred):
        conditions = pred.args
        lst = []
        for c in conditions:
            for id in self._production_id_cache[c]:
                for l in self.leafs:
                    lst.append(l.var == id)
        self.z3_solver.add(z3.Or(lst))

    def _resolve_happens_before_predicate(self, pred):
        pres = self._production_id_cache[pred.args[1]]

        for pos in self._production_id_cache[pred.args[0]]:
            for r_i in range(len(self.roots)):
                previous_roots = []
                for r_ia in range(r_i):
                    for c in self.roots[r_ia].children:
                        for pre in pres:
                            previous_roots.append(c.var == pre)

                self.z3_solver.add(
                    z3.Implies(z3.Or(*(c.var == pos for c in self.roots[r_i].children)),
                               z3.Or(previous_roots)))

    def _resolve_block_first_tree_predicate(self, pred):
        pass

    def _resolve_block_range_lower_bound_predicate(self, pred):
        pass

    def _resolve_block_range_upper_bound_predicate(self, pred):
        pass

    def _resolve_block_subtree_predicate(self, pred):
        pass

    def _resolve_block_tree_predicate(self, pred):
        pass

    def _resolve_char_must_occur_predicate(self, pred):
        pass

    def resolve_predicates(self, predicates):
        try:
            for pred in predicates:
                if pred.name == 'is_not_parent':
                    self._resolve_is_not_parent_predicate(pred)
                elif pred.name == 'distinct_inputs':
                    self._resolve_distinct_inputs_predicate(pred)
                elif pred.name == 'constant_occurs':
                    self._resolve_constant_occurs_predicate(pred)
                elif pred.name == 'happens_before':
                    self._resolve_happens_before_predicate(pred)
                elif pred.name == 'distinct_filters':
                    self._resolve_distinct_filters_predicate(pred)
                else:
                    logger.warning('Predicate not handled: {}'.format(pred))
        except (KeyError, ValueError) as e:
            msg = 'Failed to resolve predicates. {}'.format(e)
            raise RuntimeError(msg) from None

    def get_first_child(self, node, pos):
        for c_ind in range(len(node.children)):
            try:
                pos[node.children[c_ind].nb]
            except:
                return c_ind
        return len(node.children) - 1

    def find_lattices(self):
        lats = open("squares/forest/enumerator/lattices/loc-" + str(self.loc), "r+")
        lats = lats.readlines()
        for l in lats:
            lat, mods = l.split(":", 1)
            models = []
            if mods[:-1] != '':
                mods = mods[:-1].replace(" ", "").split("|", self.loc * 2)
                for m in mods:
                    if m == "":
                        continue
                    model = dict()
                    m = m[1:-1].split(",")
                    if m == ['']:
                        break
                    for c in m:
                        c = c.split("=") if "=" in c else c.split(":")
                        model[z3.Int(c[0])] = z3.Int(c[1])
                    models.append(model)
            if lat not in self.lattices:
                self.lattices[lat] = models

    def close_lattices(self):
        logger.debug('Total Solver Time: {}'.format(self.solverTime))
        if self.totalSymTime != 0:
            logger.debug('Total Time Symmetries: {}'.format(self.totalSymTime))
        if self.totalBlockedModels != 0:
            logger.debug('Total Blocked Models: {}'.format(self.totalBlockedModels))
        if self.loc < 6 or self.break_sym_online or not self.sym_breaker:
            return

        lats = open("squares/forest/enumerator/lattices/loc-" + str(self.loc), "w+")

        for l, mdls in self.lattices.items():
            st = l + ":"
            if mdls:
                for m in mdls:
                    st += str(m) + "|"

                lats.write(st[:-1] + "\n")
            else:
                lats.write(st + "[]\n")

        lats.close()

    def create_clean_tree(self, id, node):
        j = id
        node.children = []
        childs = []
        for i in range(j + 1, j + self.loc):
            l = Node(i)
            l.h = node.h + 1
            l.id = 0
            l.children = []
            id += 1
            node.children.append(l)
            childs.append(l)

        for l in node.children:
            if l.h == self.loc:
                break
            id, childs_aux = self.create_clean_tree(id, l)
            childs += childs_aux

        return id, childs

    def create_complete_lattice(self, node):
        node.children = []
        for c in self.roots[node.nb - 1].children:
            for l in c.lines:
                if self.model[l] == 1:
                    child = Node(int(str(l).split("_")[1]))
                    child.h = node.h + 1
                    self.create_complete_lattice(child)
                    node.children.append(child)

    def create_lattice(self, node, nb_root, dic):
        for c_ind in range(len(self.roots[nb_root - 1].children)):
            c = self.roots[nb_root - 1].children[c_ind]
            for l_ind in range(len(c.lines)):
                l = c.lines[l_ind]
                if self.model[l] == 1:
                    node_child = node.children[self.get_first_child(node, dic)]
                    dic[node_child.nb] = l_ind + 1
                    self.create_lattice(node_child, l_ind + 1, dic)
                    break

    def find_symmetries(self):
        pos = dict()
        pos[1] = self.loc
        root = self.cleanedTree[0]
        self.create_lattice(root, self.loc, pos)
        if not self.break_sym_online and self.loc < 6:
            try:
                return self.lattices[write_lattice(root, pos)]
            except:
                return []
        else:
            lat = write_lattice(root, pos)
            try:
                return self.lattices[lat]
            except:
                last_line = Node(self.loc)
                last_line.h = 0
                self.create_complete_lattice(last_line)
                models = self.symFinder.findSymmetries(last_line)
                self.lattices[lat] = models
                if self.loc > 5 and not self.break_sym_online:
                    self.find_lattices()
                    self.close_lattices()
                return models

    def change_node(self, node_pos, new_node_pos, new_model, model):
        root, new_root = self.roots[node_pos - 1], self.roots[int(str(new_node_pos)) - 1]

        for c in range(len(root.children)):
            val = int(str(model[root.children[c].var]))
            if val != 0:
                new_model[new_root.children[c].var] = model[root.children[c].var]
            else:
                new_model[new_root.children[c].var] = self.model[root.children[c].var]

        # change the type of the line
        new_model[new_root.type] = model[root.type]

    def from_symmetries2programs(self, model, m_aux):
        for t in range(len(self.typeVars) - 1):
            k = self.typeVars[t]
            m_aux[k] = self.model[k]  # NEW
            root_num = t + 1
            type = int(str(self.model[k]))
            new_node = int(str(model[z3.Int('x_' + str(root_num))]))
            old_prod = self.line_productions[root_num - 1][type].id
            new_prod = self.line_productions[new_node - 1][type].id
            start = root_num * self.max_children
            for i in range(start, len(self.leafs)):
                n = self.leafs[i]
                if self.model[n.var] == old_prod:
                    m_aux[n.var] = z3.IntVal(new_prod)
                    break
        m_aux[self.typeVars[-1]] = self.model[self.typeVars[-1]]

        n_model = dict(m_aux)
        for v in model:
            var, new_node_pos = v, int(str(model[v]))
            node_pos = int(str(var).split("_")[1])
            n_model[self.roots[new_node_pos - 1].var] = self.model[
                self.roots[node_pos - 1].var]
            self.change_node(node_pos, new_node_pos, n_model, m_aux)

        n_model[self.roots[-1].var] = self.model[self.roots[-1].var]
        self.change_node(0, 0, n_model, m_aux)

        return n_model

    def get_model_constraint(self):
        block = []
        for x in self.variables:
            block.append(x != z3.Int('val_' + str(x)))
        self.modelConstraint = z3.Or(block)

        for m in self.model:
            self.cleanedModel[m()] = z3.IntVal(0)

    def block_model_aux(self, model):
        # block the model using only the variables that correspond to productions (nodes = leafs + roots)
        const = z3.substitute(self.modelConstraint,
                              [(z3.Int(f'val_{str(x)}'), model[x]) for x in
                               self.variables])
        self.z3_solver.add(const)

    def block_model(self):
        assert (self.model is not None)
        # in order to find symmetric programs
        self.block_model_aux(self.model)

        if self.sym_breaker and self.loc > 2:
            time_1 = time.time()
            models_sols = self.find_symmetries()

            if len(models_sols) > 0:
                for mdl in models_sols:
                    m_2 = dict(self.cleanedModel)
                    m = self.from_symmetries2programs(mdl, m_2)
                    self.block_model_aux(m)
                    self.blockedModels += 1
            self.symTime = time.time() - time_1  # EQUAL NOT PLUS EQUAL
            self.totalSymTime += self.symTime

    def update(self, info=None, id=None):
        self.blockedModels = 0
        self.block_model()
        self.totalBlockedModels += self.blockedModels
        if self.blockedModels != 0:
            logger.error('Total Blocked Models: {}'.format(self.totalBlockedModels))
            logger.error('Total Time Symmetries: {}'.format(self.totalSymTime))

    def make_node(self, c, builder_nodes, builder):
        if str(c.production).find('Empty') == -1:
            if c.children is None:
                builder_nodes[c.nb - 1] = builder.make_node(c.production.id, [])
                self.program2tree[builder_nodes[c.nb - 1]] = c.var
            else:
                children = []
                for r_c in c.children:
                    if builder_nodes[r_c.nb - 1] is None:
                        self.make_node(r_c, builder_nodes, builder)

                    children.append(builder_nodes[r_c.nb - 1])
                    self.program2tree[builder_nodes[r_c.nb - 1]] = r_c.var

                builder_nodes[c.nb - 1] = builder.make_node(c.production.id,
                                                            [c for c in children if
                                                             c is not None])
                self.program2tree[builder_nodes[c.nb - 1]] = c.var

    def build_program(self):
        model = self.model
        roots = deepcopy(self.roots)
        self.program2tree.clear()

        for r in roots:
            r.production = self.spec.get_production(model[r.var].as_long())
            for c in r.children:
                c.production = self.spec.get_production(model[c.var].as_long())
                if c.production is None:
                    for l in c.lines:
                        if model[l] == 1:
                            s = f"line_{str(l).split('_')[1]}"
                            c.production = s
                            break

        builder = D.Builder(self.spec)
        num_nodes = self.roots + self.leafs
        builder_nodes = [None] * len(num_nodes)

        for r in roots:
            for c in range(len(r.children)):
                if "line_" in str(r.children[c].production):
                    root = int(r.children[c].production.split("_")[1]) - 1
                    r.children[c] = roots[root]
            self.make_node(r, builder_nodes, builder)

        self.current_roots = roots  # TODO hack
        return builder_nodes[roots[-1].nb - 1]

    def next(self):
        start_time = time.time()
        res = self.z3_solver.check()

        self.solverTime += time.time() - start_time
        if res != z3.sat:
            return None

        self.model = self.z3_solver.model()

        if self.model is not None:
            return self.build_program()
        else:
            return None

    def __str__(self):
        base = super(LinesEnumerator, self).__str__()
        return f'{base}(loc={self.loc})'
