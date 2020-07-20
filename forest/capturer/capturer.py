import re
from typing import Iterable

import re
from typing import Iterable

import z3

from forest.dsl import Node
from forest.utils import all_sublists_n, is_float, is_int, make_z3_and
from forest.visitor import RegexInterpreter


def elementwise_eq(arg1, arg2):
    for i in range(len(arg1)):
        if arg1[i] != arg2[i]:
            return False
    return True


class Capturer:
    """ capturer is one who, or that which, captures """

    def __init__(self, strings, captures, condition_invalid):
        self.strings = strings
        self.captures = captures
        self.condition_invalid = condition_invalid
        self.interpreter = RegexInterpreter()
        self.capture_bounds = []
        self.conditions = ['le', 'ge']
        self.as_valid = []
        self.as_invalid = []
        self.ss = {}

    def synthesize_capturing_groups(self, regex: Node):
        if len(self.captures) == 0 or len(self.captures[0]) == 0:
            return []
        nodes = regex.get_leaves()
        # try placing a capture group in each node
        interpreter = RegexInterpreter()
        for sub in all_sublists_n(nodes, len(self.captures[0])):
            regex_str = interpreter.eval(regex, captures=sub)
            compiled_re = re.compile(regex_str)
            if not all(
                    map(lambda s: compiled_re.fullmatch(s[0]) is not None, self.strings)):
                continue
            if all(map(lambda i:
                       elementwise_eq(compiled_re.fullmatch(self.strings[i][0]).groups(),
                                      self.captures[i]), range(len(self.strings)))):
                return sub
        return None

    def synthesize_capture_conditions(self, regex: Node):
        if len(self.captures) == 0 or len(self.captures[0]) == 0:
            return []
        nodes = regex.get_leaves()
        # try placing a capture group in each node

        regex_str = self.interpreter.eval(regex)
        compiled_re = re.compile(regex_str)
        if not all(map(lambda s: compiled_re.fullmatch(s[0]), self.strings)):
            raise ValueError("Regex doesn't match all valid examples")
        if not all(map(lambda s: compiled_re.fullmatch(s[0]), self.condition_invalid)):
            raise ValueError("Regex doesn't match all condition invalid examples")
        for n in range(1, len(nodes)):
            for sub in all_sublists_n(nodes, n):
                regex_str = self.interpreter.eval(regex, captures=sub)
                compiled_re = re.compile(regex_str)
                if not all(map(lambda ex: compiled_re.fullmatch(ex[0]), self.strings)):
                    continue
                if not all(map(lambda ex: all(map(lambda g: is_int(g) or is_float(g),
                                                  compiled_re.fullmatch(ex[0]).groups())),
                               self.strings)):
                    continue
                a = self._synth_conditions(regex, sub)
                if a == 1:
                    return

    def create_le_constraint(self, values: Iterable[int], bound, u_bool):
        big_and = []
        for val in values:
            z3_val = z3.IntVal(val)
            big_and.append(z3.Implies(u_bool, z3_val <= bound))
        return make_z3_and(big_and)

    def create_ge_constraint(self, values: Iterable[int], bound, u_bool):
        big_and = []
        for val in values:
            z3_val = z3.IntVal(val)
            big_and.append(z3.Implies(u_bool, z3_val >= bound))
        return make_z3_and(big_and)

    def _synth_conditions(self, regex, captures):
        solver = z3.Optimize()
        regex_str = self.interpreter.eval(regex, captures=captures)
        print(regex_str)
        cap_upper_bounds = []
        cap_lower_bounds = []
        for i, cap in enumerate(captures):
            upper_bound = z3.Int(f"cap{i}_le")
            cap_upper_bounds.append(upper_bound)
            lower_bound = z3.Int(f"cap{i}_ge")
            cap_lower_bounds.append(lower_bound)
        compiled_re = re.compile(regex_str)
        valid_as = []

        for ex_idx, ex in enumerate(self.strings):
            captures = compiled_re.fullmatch(ex[0]).groups()
            s_caps = []
            ex_letter = 'v'
            for cap_idx, cap in enumerate(captures):
                # a_x <-> big_and s_cap
                self.make_cap_constraint(cap_idx, cap_lower_bounds, cap_upper_bounds,
                                         captures, ex_idx, ex_letter, s_caps, solver)
            a_x = z3.Bool(f"a_{ex_letter}{ex_idx}")
            valid_as.append(a_x)
            solver.add(a_x == make_z3_and(s_caps))

        solver.add(make_z3_and(valid_as))

        invalid_as = []
        for ex_idx, ex in enumerate(self.condition_invalid):
            captures = compiled_re.fullmatch(ex[0]).groups()
            s_caps = []
            ex_letter = 'i'
            for cap_idx, cap in enumerate(captures):
                # a_x <-> big_and s_cap
                self.make_cap_constraint(cap_idx, cap_lower_bounds, cap_upper_bounds,
                                         captures, ex_idx, ex_letter, s_caps, solver)
            a_x = z3.Bool(f"a_{ex_letter}{ex_idx}")
            invalid_as.append(z3.Not(a_x))
            solver.add(a_x == make_z3_and(s_caps))
        solver.add(make_z3_and(invalid_as))

        for cap_idx, cap in enumerate(captures):
            u = z3.Bool(f"u_cap{cap_idx}_le")
            solver.add_soft(z3.Not(u))
            u = z3.Bool(f"u_cap{cap_idx}_le")
            solver.add_soft(z3.Not(u))
        res = solver.check()
        if res == z3.sat:
            print(solver.model())
            for cap_idx in range(len(captures)):
                lower_bound = solver.model()[cap_lower_bounds[cap_idx]]
                print(f"${cap_idx} >= {lower_bound}")
                upper_bound = solver.model()[cap_upper_bounds[cap_idx]]
                print(f"${cap_idx} <= {upper_bound}")
            return 1
        else:
            print("unsat")
            return 0

    def make_cap_constraint(self, cap_idx, cap_lower_bounds, cap_upper_bounds, captures,
                            ex_idx, ex_letter, s_caps, solver):
        s_cap_and = []
        u = z3.Bool(f"u_cap{cap_idx}_le")
        ctr = self.create_le_constraint(map(int, captures),
                                        cap_upper_bounds[cap_idx], u)
        # solver.add(ctr)
        s_cap_and.append(ctr)
        u = z3.Bool(f"u_cap{cap_idx}_ge")
        ctr = self.create_ge_constraint(map(int, captures),
                                        cap_lower_bounds[cap_idx], u)
        # solver.add(ctr)
        s_cap_and.append(ctr)
        s_cap = z3.Bool(f"s_cap{cap_idx}_{ex_letter}{ex_idx}")
        s_caps.append(s_cap)
        solver.add(s_cap == make_z3_and(s_cap_and))
