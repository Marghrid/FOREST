import re
from copy import deepcopy
from typing import List, Tuple

import z3

from forest import utils
from forest.dsl import Node
from forest.visitor import RegexInterpreter


def keep_distinct(list1: List, list2: List):
    list1_copy = deepcopy(list1)
    list2_copy = deepcopy(list2)
    for el in list1:
        if el in list2_copy:
            list1_copy.remove(el)
            list2_copy.remove(el)
    return list1_copy, list2_copy


class ConditionDistinguisher:
    def __init__(self, regex: Node, capture_groups: List, valid_example: str):
        self._regex = regex
        self._capture_groups = capture_groups
        self._valid_example = valid_example
        self._interpreter = RegexInterpreter()

        self.condition_operators = utils.condition_operators

    def distinguish(self, model1: List[Tuple], model2: List[Tuple]):
        solver = z3.Solver()
        model1_copy, model2_copy = keep_distinct(model1, model2)
        cs = []
        sat_m1 = z3.Bool("sat_m1")
        sat_m2 = z3.Bool("sat_m2")
        for cap_idx in range(len(self._capture_groups)):
            cs.append(z3.Int(f"c{cap_idx}"))

        solver.add(self._get_sat_m_constraint(cs, model1_copy, sat_m1))
        solver.add(self._get_sat_m_constraint(cs, model2_copy, sat_m2))

        solver.add(z3.Xor(sat_m1, sat_m2))

        if solver.check() == z3.sat:
            valid_ex = self._valid_example
            for c_idx, c_var in enumerate(cs):
                if solver.model()[c_var] is None:
                    continue
                c_val = str(solver.model()[c_var])
                regex_str = self._interpreter.eval(self._regex,
                                                   captures=[self._capture_groups[c_idx]])
                compiled_re = re.compile(regex_str)
                cap_substr = compiled_re.fullmatch(valid_ex).groups()[0]
                c_val = c_val.rjust(len(cap_substr), '0')
                valid_ex = valid_ex.replace(cap_substr, c_val, 1)
                if solver.model()[sat_m1]:
                    return valid_ex, model1, model2
                else:
                    return valid_ex, model2, model1

        else:
            return None, None, None

    def _get_sat_m_constraint(self, cs, model, sat_m):
        big_and = []
        for cond_ctr in model:
            c_i = cs[cond_ctr[0]]
            cond = cond_ctr[1]
            bound_val = cond_ctr[2]
            big_and.append(self._get_reverse_cond(cond, bound_val, c_i))
        return sat_m == z3.And(big_and)

    def _get_reverse_cond(self, cond: str, bound: z3.IntNumRef, cap_var: z3.IntNumRef):
        op = self.condition_operators[cond]
        return op(cap_var, bound)
