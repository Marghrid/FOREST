import re
from typing import List, Iterable, Optional

import z3
from termcolor import colored

from forest import utils
from forest.distinguisher import ConditionDistinguisher
from forest.dsl import Node
from forest.logger import get_logger
from forest.utils import all_sublists_n, is_float, is_int, make_z3_and, yes_values, \
    no_values
from forest.visitor import RegexInterpreter

logger = get_logger('forest')


def elementwise_eq(arg1, arg2):
    for i in range(len(arg1)):
        if arg1[i] != arg2[i]:
            return False
    return True


class Capturer:
    """ 'capturer is one who, or that which, captures' """

    def __init__(self, valid, captures, condition_invalid):
        self.valid = valid
        self.captures = captures
        self.condition_invalid = condition_invalid
        self.interpreter = RegexInterpreter()
        self.condition_operators = utils.condition_operators
        self.conditions = list(self.condition_operators.keys())
        self.as_valid = []
        self.as_invalid = []
        self.bounds = {}
        self.ss_valid = {}
        self.ss_invalid = {}
        self.us = {}

    def synthesize_capturing_groups(self, regex: Node):
        """ It finds capturing groups in regex which math self.captures """
        if len(self.captures) == 0 or len(self.captures[0]) == 0:
            return []
        nodes = regex.get_leaves()
        # try placing a capture group in each node
        for sub in all_sublists_n(nodes, len(self.captures[0])):
            regex_str = self.interpreter.eval(regex, captures=sub)
            compiled_re = re.compile(regex_str)
            if not all(
                    map(lambda s: compiled_re.fullmatch(s[0]) is not None, self.valid)):
                continue
            if all(map(lambda i:
                       elementwise_eq(compiled_re.fullmatch(self.valid[i][0]).groups(),
                                      self.captures[i]), range(len(self.valid)))):
                return sub
        return None

    def synthesize_capture_conditions(self, regex: Node):
        if len(self.condition_invalid) == 0:
            return [], []
        nodes = regex.get_leaves()
        regex_str = self.interpreter.eval(regex)
        compiled_re = re.compile(regex_str)
        # Test that regex satisfies
        if not all(map(lambda ex: compiled_re.fullmatch(ex[0]), self.valid)):
            raise ValueError("Regex doesn't match all valid examples")
        if not all(map(lambda s: compiled_re.fullmatch(s[0]), self.condition_invalid)):
            raise ValueError("Regex doesn't match all condition invalid examples")

        for n in range(1, len(nodes)):
            for sub in all_sublists_n(nodes, n):
                regex_str = self.interpreter.eval(regex, captures=sub)
                compiled_re = re.compile(regex_str)
                l = list(
                    map(lambda ex: compiled_re.fullmatch(ex[0]) is not None, self.valid))
                if not all(map(lambda ex: compiled_re.fullmatch(ex[0]) is not None,
                               self.valid)):
                    continue
                if not all(map(lambda ex:
                               all(map(lambda g: is_int(g) or is_float(g),
                                       compiled_re.fullmatch(ex[0]).groups())),
                               self.valid)):
                    continue
                condition = self._synthesize_conditions_for_captures(regex, sub)
                if condition is not None:
                    return condition, sub
        return None, None

    def _synthesize_conditions_for_captures(self, regex, capture_groups):
        assert len(self.condition_invalid)
        solver = z3.Optimize()
        self._init_z3_variables(capture_groups)
        condition_distinguisher = ConditionDistinguisher(regex, capture_groups,
                                                         self.valid[0][0])
        num_captures = len(capture_groups)

        regex_str = self.interpreter.eval(regex, captures=capture_groups)
        compiled_re = re.compile(regex_str)

        solver.add(self._make_a_constraints(compiled_re, solver, self.valid, valid=True))
        solver.add(self._make_a_constraints(compiled_re, solver, self.condition_invalid,
                                            valid=False))

        # Soft clauses to minimize the number of used conditions:
        for u in self.us.values():
            solver.add_soft(z3.Not(u))

        conditions = []
        while True:
            new_condition = self._next_condition(solver, num_captures)
            if new_condition is not None:
                self._block_model(solver, solver.model(), num_captures)
                conditions.append(new_condition)
                if len(conditions) > 1:
                    dist_input, keep_if_valid, keep_if_invalid = condition_distinguisher.distinguish(
                        conditions[0], conditions[1])
                    conditions = self._interact(dist_input, keep_if_valid,
                                                keep_if_invalid)
            else:
                if len(conditions) == 0:
                    return None
                else:
                    assert len(conditions) == 1
                    return conditions[0]

    def _make_a_constraints(self, compiled_re, solver: z3.Optimize, examples: List,
                            valid: bool):
        for ex_idx, ex in enumerate(examples):
            captured = compiled_re.fullmatch(ex[0]).groups()
            ss_of_this_x = []
            for cap_idx, cap in enumerate(captured):
                # a_x <-> big_and s_cap
                s, ctr = self._get_s_and_s_constraint(cap_idx, captured, ex_idx, valid)
                solver.add(ctr)
                ss_of_this_x.append(s)
            if valid:
                a_x = self.as_valid[ex_idx]
            else:
                a_x = self.as_invalid[ex_idx]
            solver.add(a_x == make_z3_and(ss_of_this_x))
        if valid:
            return make_z3_and(self.as_valid)
        else:
            return make_z3_and(list(map(z3.Not, self.as_invalid)))

    def _get_condition_from_model(self, num_captures: int, model):
        ret = []
        for cap_idx in range(num_captures):
            for cond in self.conditions:
                u = model[self.us[(cap_idx, cond)]]
                if u:
                    bound = model[self.bounds[(cap_idx, cond)]]
                    ret.append((cap_idx, cond, bound))
        return ret

    def _init_z3_variables(self, captures):
        # a vars:
        self.as_valid = []
        self.as_invalid = []
        for ex_idx, ex in enumerate(self.valid):
            self.as_valid.append(z3.Bool(self._get_a_var_name(ex_idx, valid=True)))
        for ex_idx, ex in enumerate(self.condition_invalid):
            self.as_invalid.append(z3.Bool(self._get_a_var_name(ex_idx, valid=False)))
        # s vars:
        self.ss_valid = {}
        self.ss_invalid = {}
        for cap_idx in range(len(captures)):
            for ex_idx, ex in enumerate(self.valid):
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

    def _get_cond(self, cap_idx: int, cond: str, val: int):
        z3_val = z3.IntVal(val)
        op = self.condition_operators[cond]
        return op(z3_val, self.bounds[(cap_idx, cond)])

    def _get_s_and_s_constraint(self, cap_idx: int, captures: Iterable[str], ex_idx: int,
                                valid: bool):
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

    def _next_condition(self, solver, num_captures) -> Optional[List[tuple]]:
        if solver.check() == z3.sat:
            return self._get_condition_from_model(num_captures, solver.model())
        else:
            return None

    def _block_model(self, solver, model, num_captures):
        big_or = []
        for cap_idx in range(num_captures):
            for cond in self.conditions:
                u = model[self.us[(cap_idx, cond)]]
                if u:
                    bound = model[self.bounds[(cap_idx, cond)]]
                    big_or.append(self.bounds[(cap_idx, cond)] != bound)
        solver.add(z3.Or(big_or))

    def _interact(self, dist_input, keep_if_valid, keep_if_invalid):
        """ Interact with user to ascertain whether the distinguishing input is valid """
        # Do not count time spent waiting for user input: add waiting time to start_time.
        while True:
            x = input(f'Is "{dist_input}" valid?\n')
            if x.lower().rstrip() in yes_values:
                logger.info(f'"{dist_input}" is {colored("valid", "green")}.')
                self.valid.append([dist_input])
                return [keep_if_valid]
            elif x.lower().rstrip() in no_values:
                logger.info(f'"{dist_input}" is {colored("conditional invalid", "red")}.')
                self.condition_invalid.append([dist_input])
                return [keep_if_invalid]
            else:
                logger.info(f"Invalid answer {x}! Please answer 'yes' or 'no'.")
