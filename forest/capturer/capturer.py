import operator
import re
from typing import List

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
        self.conditions = ['<=', '>=']
        self.condition_operators = {'<=': operator.le, '>=': operator.ge}
        self.as_valid = []
        self.as_invalid = []
        self.bounds = {}
        self.ss_valid = {}
        self.ss_invalid = {}
        self.us = {}

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

    def _synth_conditions(self, regex, captures):
        solver = z3.Optimize()
        self._init_z3_variables(captures)

        regex_str = self.interpreter.eval(regex, captures=captures)
        print(regex_str)
        compiled_re = re.compile(regex_str)

        for ex_idx, ex in enumerate(self.strings):
            captures = compiled_re.fullmatch(ex[0]).groups()
            ss_of_this_x = []
            for cap_idx, cap in enumerate(captures):
                # a_x <-> big_and s_cap
                s, ctr = self._get_s_and_s_constraint(cap_idx, captures, ex_idx, True)
                solver.add(ctr)
                ss_of_this_x.append(s)
            a_x = self.as_valid[ex_idx]
            solver.add(a_x == make_z3_and(ss_of_this_x))

        solver.add(make_z3_and(self.as_valid))

        for ex_idx, ex in enumerate(self.condition_invalid):
            captures = compiled_re.fullmatch(ex[0]).groups()
            ss_of_this_x = []
            for cap_idx, cap in enumerate(captures):
                # a_x <-> big_and s_cap
                s, ctr = self._get_s_and_s_constraint(cap_idx, captures, ex_idx, False)
                solver.add(ctr)
                ss_of_this_x.append(s)
            a_x = self.as_invalid[ex_idx]
            solver.add(a_x == make_z3_and(list(ss_of_this_x)))

        solver.add(make_z3_and(list(map(z3.Not, self.as_invalid))))

        for u in self.us.values():
            solver.add_soft(z3.Not(u))

        res = solver.check()
        if res == z3.sat:
            # print(solver.model())
            self._print_result(captures, solver.model())
            return 1
        else:
            print("unsat")
            return 0

    def _print_result(self, captures, model):
        for cap_idx in range(len(captures)):
            for cond in self.conditions:
                u = model[self.us[(cap_idx, cond)]]
                if u:
                    bound = model[self.bounds[(cap_idx, cond)]]
                    print(f"${cap_idx} {cond} {bound}")

    def _init_z3_variables(self, captures):
        # a vars:
        self.as_valid = []
        self.as_invalid = []
        for ex_idx, ex in enumerate(self.strings):
            self.as_valid.append(z3.Bool(self._get_a_var_name(ex_idx, valid=True)))
        for ex_idx, ex in enumerate(self.condition_invalid):
            self.as_invalid.append(z3.Bool(self._get_a_var_name(ex_idx, valid=False)))
        # s vars:
        self.ss_valid = {}
        self.ss_invalid = {}
        for cap_idx in range(len(captures)):
            for ex_idx, ex in enumerate(self.strings):
                self.ss_valid[(cap_idx, ex_idx)] = \
                    z3.Bool(self._get_s_var_name(cap_idx, ex_idx, True))
            for ex_idx, ex in enumerate(self.condition_invalid):
                self.ss_invalid[(cap_idx, ex_idx)] = \
                    z3.Bool(self._get_s_var_name(cap_idx, ex_idx, False))
        # u vars
        self.us = {}
        for cond in self.conditions:
            for cap_idx in range(len(captures)):
                self.us[(cap_idx, cond)] = z3.Bool(self._get_u_var_name(cap_idx, cond))
        # bounds
        self.bounds = {}
        for cap_idx, cap in enumerate(captures):
            for cond in self.conditions:
                bound = z3.Int(f"cap{cap_idx}_{cond}")
                self.bounds[(cap_idx, cond)] = bound

    def _get_u_implies(self, cond: str, cap_idx: int, values: List[int]):
        return z3.Implies(self.us[(cap_idx, cond)],
                          self._get_cond(cap_idx, cond, values[cap_idx]))

    def _get_cond(self, cap_idx, cond, val):
        z3_val = z3.IntVal(val)
        op = self.condition_operators[cond]
        return op(z3_val, self.bounds[(cap_idx, cond)])

    def _get_s_and_s_constraint(self, cap_idx, captures, ex_idx, valid):
        s_big_and = []
        for cond in self.conditions:
            ctr = self._get_u_implies(cond, cap_idx, list(map(int, captures)))
            s_big_and.append(ctr)
        if valid:
            s = self.ss_valid[(cap_idx, ex_idx)]
        else:
            s = self.ss_invalid[(cap_idx, ex_idx)]
        return s, s == make_z3_and(s_big_and)

    def _get_a_var_name(self, ex_idx: int, valid: bool):
        if valid:
            ex_letter = 'v'
        else:
            ex_letter = 'i'
        return f"a_{ex_letter}{ex_idx}"

    def _get_s_var_name(self, cap_idx: int, ex_idx: int, valid: bool):
        if valid:
            ex_letter = 'v'
        else:
            ex_letter = 'i'
        return f"s_cap{cap_idx}_{ex_letter}{ex_idx}"

    def _get_u_var_name(self, cap_idx: int, condition: str):
        return f"u_cap{cap_idx}_{condition}"
