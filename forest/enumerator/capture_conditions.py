import re
from typing import Optional, List, Iterable

import z3

from forest import utils
from forest.utils import make_z3_and, transpose


class CaptureConditionsEnumerator:
    def __init__(self, regex_str, num_captures: int, valid: List[List[str]], condition_invalid: List[List[str]]):
        self.solver = z3.Optimize()
        self.num_captures = num_captures

        self.condition_operators = utils.condition_operators
        self.conditions = list(self.condition_operators.keys())

        valid = list(map(lambda x: x[0], valid))
        assert isinstance(valid, List) and isinstance(valid[0], str)
        condition_invalid = list(map(lambda x: x[0], condition_invalid))
        assert isinstance(condition_invalid, List) and isinstance(condition_invalid[0], str)

        self.compiled_re = re.compile(regex_str)
        self.model = None

        self._init_z3_variables(valid, condition_invalid)
        self._init_max_min(valid, condition_invalid)

        self.solver.add(self._make_a_constraints(valid, valid=True))
        self.solver.add(self._make_a_constraints(condition_invalid, valid=False))

        # Soft clauses to minimize the number of used conditions:
        for u in self.us.values():
            self.solver.add_soft(z3.Not(u))

    def next(self) -> Optional[List[tuple]]:
        # This was an attempt to simulate binary search, but it failed:
        # for c in range(self.num_captures):
        #     avg_max = (self.max_cap_valid[c] + self.max_cap_cond_invalid[c])//2
        #     print(f"avg max ${c}", avg_max)
        #     self.solver.minimize(z3_abs(self.bounds[(c, "<=")] - z3.IntVal(avg_max)))
        #
        #     avg_min = (self.min_cap_valid[c] + self.min_cap_cond_invalid[c]) // 2
        #     print(f"avg min ${c}", avg_min)
        #     self.solver.minimize(z3_abs(self.bounds[(c, "<=")] - z3.IntVal(avg_min)))

        if self.solver.check() == z3.sat:
            self.model = self.solver.model()
            return self._get_condition_from_model()
        else:
            return None

    def _get_condition_from_model(self):
        condition = []
        for cap_idx in range(self.num_captures):
            for cond in self.conditions:
                if self.model[self.us[(cap_idx, cond)]]:
                    bound = self.model[self.bounds[(cap_idx, cond)]]
                    condition.append((cap_idx, cond, int(str(bound))))
        return condition

    def update(self):
        assert self.model
        big_or = []
        for cap_idx in range(self.num_captures):
            for cond in self.conditions:
                u = self.model[self.us[(cap_idx, cond)]]
                if u:
                    bound = self.model[self.bounds[(cap_idx, cond)]]
                    big_or.append(self.bounds[(cap_idx, cond)] != bound)
        self.solver.add(z3.Or(big_or))

    def _init_z3_variables(self, valid, condition_invalid):
        # a vars:
        self.as_valid = {}
        self.as_invalid = {}
        for ex in valid:
            self.as_valid[ex] = z3.Bool(self._get_a_var_name(ex, valid=True))
        for ex in condition_invalid:
            self.as_invalid[ex] = z3.Bool(self._get_a_var_name(ex, valid=False))

        # s vars:
        self.ss_valid = {}
        self.ss_invalid = {}
        for cap_idx in range(self.num_captures):
            for ex in valid:
                self.ss_valid[(cap_idx, ex)] = z3.Bool(self._get_s_var_name(cap_idx, ex, True))
            for ex in condition_invalid:
                self.ss_invalid[(cap_idx, ex)] = z3.Bool(self._get_s_var_name(cap_idx, ex, False))

        # u vars
        self.us = {}
        for cond in self.conditions:
            for cap_idx in range(self.num_captures):
                self.us[(cap_idx, cond)] = z3.Bool(self._get_u_var_name(cap_idx, cond))

        # bounds
        self.bounds = {}
        for cap_idx in range(self.num_captures):
            for cond in self.conditions:
                bound = z3.Int(f"cap{cap_idx}_{cond}")
                self.bounds[(cap_idx, cond)] = bound

    def _get_u_implies(self, cond: str, cap_idx: int, values: List[int]):
        return z3.Implies(self.us[(cap_idx, cond)],
                          self._get_cond(cap_idx, cond, values[cap_idx]))

    def _get_cond(self, cap_idx: int, cond: str, val: int):
        z3_val = z3.IntVal(val)
        op = self.condition_operators[cond]
        return op(z3_val, self.bounds[(cap_idx, cond)])

    def _get_s_and_s_constraint(self, cap_idx: int, captures: Iterable[str], ex: str, valid: bool):
        s_big_and = []
        for cond in self.conditions:
            ctr = self._get_u_implies(cond, cap_idx, list(map(int, captures)))
            s_big_and.append(ctr)
        s = self.ss_valid[(cap_idx, ex)] if valid else self.ss_invalid[(cap_idx, ex)]
        return s, s == make_z3_and(s_big_and)

    def _get_a_var_name(self, ex: str, valid: bool):
        ex_letter = 'v' if valid else 'i'
        return f"a_{ex_letter}{ex}"

    def _get_s_var_name(self, cap_idx: int, ex: str, valid: bool):
        ex_letter = 'v' if valid else 'i'
        return f"s_cap{cap_idx}_{ex_letter}{ex}"

    def _get_u_var_name(self, cap_idx: int, condition: str):
        return f"u_cap{cap_idx}_{condition}"

    def _make_a_constraints(self, examples: List, valid: bool):
        for ex in examples:
            captured = self.compiled_re.fullmatch(ex).groups()
            ss_of_this_x = []
            for cap_idx in range(len(captured)):
                # a_x <-> big_and s_cap
                s, ctr = self._get_s_and_s_constraint(cap_idx, captured, ex, valid)
                self.solver.add(ctr)
                ss_of_this_x.append(s)
            a_x = self.as_valid[ex] if valid else self.as_invalid[ex]
            self.solver.add(a_x == make_z3_and(ss_of_this_x))
        return make_z3_and(list(self.as_valid.values())) if valid \
            else make_z3_and(list(map(z3.Not, self.as_invalid.values())))

    def add_valid(self, new_valid: str):
        """ Add a new valid example to Capturer. """
        self.as_valid[new_valid] = z3.Bool(self._get_a_var_name(new_valid, valid=True))
        for cap_idx in range(self.num_captures):
            self.ss_valid[(cap_idx, new_valid)] = z3.Bool(self._get_s_var_name(cap_idx, new_valid, True))
        self.solver.add(self._make_a_constraints([new_valid], valid=True))

        new_captures = list(map(int, self.compiled_re.fullmatch(new_valid).groups()))
        for i in range(len(new_captures)):
            if new_captures[i] > self.max_cap_valid[i]:
                self.max_cap_valid[i] = new_captures[i]
            if new_captures[i] < self.min_cap_valid[i]:
                self.min_cap_valid[i] = new_captures[i]

    def add_conditional_invalid(self, new_cond_invalid: str):
        self.as_invalid[new_cond_invalid] = z3.Bool(self._get_a_var_name(new_cond_invalid, valid=False))
        for cap_idx in range(self.num_captures):
            self.ss_invalid[(cap_idx, new_cond_invalid)] = z3.Bool(
                self._get_s_var_name(cap_idx, new_cond_invalid, False))
        self.solver.add(self._make_a_constraints([new_cond_invalid], valid=False))

        new_captures = list(map(int, self.compiled_re.fullmatch(new_cond_invalid).groups()))
        for i in range(len(new_captures)):
            if new_captures[i] > self.max_cap_cond_invalid[i]:
                self.max_cap_cond_invalid[i] = new_captures[i]
            if new_captures[i] < self.min_cap_cond_invalid[i]:
                self.min_cap_cond_invalid[i] = new_captures[i]

    def _init_max_min(self, valid, condition_invalid):
        captured_valid = transpose(map(lambda ex: map(int, self.compiled_re.fullmatch(ex).groups()), valid))
        self.max_cap_valid = list(map(max, captured_valid))
        self.min_cap_valid = list(map(min, captured_valid))

        captured_cond_invalid = transpose(
            map(lambda ex: map(int, self.compiled_re.fullmatch(ex).groups()), condition_invalid))
        self.max_cap_cond_invalid = list(map(max, captured_cond_invalid))
        self.min_cap_cond_invalid = list(map(min, captured_cond_invalid))
