import re
from copy import deepcopy
from itertools import combinations
from typing import List, Tuple

import z3

from forest import utils
from forest.dsl import Node
from forest.logger import get_logger
from forest.visitor import RegexInterpreter

logger = get_logger('forest')


def keep_distinct(l: List[List]):
    """
    Given list of lists l, returns list of lists containing, for each list in l, only the elements
    that are not present in every other list.
    Example:
        l = [[1, 2, 3, 4, 5, 6, 7],
             [1, 2, 3, 5, 6, 7, 8],
             [1, 3, 4, 5, 6, 7, 9]]
        keep_distinct(l) = [[2, 4], [2, 8], [4, 9]]
    """
    l_copy = deepcopy(l)
    base = l[0]
    for el in base:
        if all(map(lambda l: el in l, l_copy)):
            for l_c in l_copy:
                l_c.remove(el)
    return l_copy


class ConditionDistinguisher:
    def __init__(self, regex: Node, capture_groups: List, valid_example: str):
        self._regex = regex
        self._capture_groups = capture_groups
        self._valid_example = valid_example
        self._interpreter = RegexInterpreter()
        self.condition_operators = utils.condition_operators

    def distinguish(self, models: List[List[Tuple]]):
        """ Find distinguishing input for sets of conditions in models """
        solver = z3.Optimize()
        distinct_models = keep_distinct(models)
        cs = []
        logger.info(f"Distinguishing {distinct_models}")
        for cap_idx in range(len(self._capture_groups)):
            cs.append(z3.Int(f"c{cap_idx}"))

        sat_ms = []
        for m_idx, model in enumerate(distinct_models):
            sat_ms.append(z3.Bool(f"sat_m{m_idx}"))
            solver.add(self._get_sat_m_constraint(cs, model, sat_ms[m_idx]))

        # solver.add(z3.Xor(sat_m1, sat_m2)) # For conversational clarification
        big_or = []
        for m_i, m_j in combinations(sat_ms, 2):  # maximisation objective from multi-distinguish
            big_or.append(z3.Xor(m_i, m_j))
            solver.add_soft(z3.Xor(m_i, m_j))
        solver.add(z3.Or(big_or))  # at least one set of conditions is distinguished from the rest

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
            keep_if_valid = []
            keep_if_invalid = []
            for m_idx in range(len(distinct_models)):
                if solver.model()[sat_ms[m_idx]]:
                    keep_if_valid.append(models[m_idx])
                else:
                    keep_if_invalid.append(models[m_idx])
            logger.info(f"Dist. input: {valid_ex}")
            return valid_ex, keep_if_valid, keep_if_invalid

        else:
            logger.info(f"Indistinguishable")
            return None, None, None

    def _get_sat_m_constraint(self, cs, model, sat_m):
        big_and = []
        for cond_ctr in model:
            c_idx, cond, bound_val = cond_ctr
            c_i = cs[c_idx]
            big_and.append(self._get_reverse_cond(cond, bound_val, c_i))
        return sat_m == z3.And(big_and)

    def _get_reverse_cond(self, cond: str, bound: z3.IntNumRef, cap_var: z3.IntNumRef):
        op = self.condition_operators[cond]
        return op(cap_var, bound)
