import re
from typing import List, Optional

from termcolor import colored

from forest.distinguisher import ConditionDistinguisher
from forest.dsl import Node
from forest.enumerator.capture_conditions import CaptureConditionsEnumerator
from forest.logger import get_logger
from forest.utils import all_sublists_n, is_float, is_int, yes_values, \
    no_values, condition_operators
from forest.visitor import RegexInterpreter

logger = get_logger('forest')


def elementwise_eq(arg1, arg2):
    for i in range(len(arg1)):
        if arg1[i] != arg2[i]:
            return False
    return True


class Capturer:
    """ 'capturer is one who, or that which, captures' """

    def __init__(self, valid: List[List[str]], captures: List[List[Optional[str]]],
                 condition_invalid: List[List[str]], ground_truth_regex: str,
                 ground_truth_conditions: List[str], auto_interact: bool):
        self.valid = valid
        self.captures = captures
        self.condition_invalid = condition_invalid
        self.ground_truth_regex = ground_truth_regex
        self.ground_truth_conditions = ground_truth_conditions
        self.auto_interact = auto_interact
        self.interpreter = RegexInterpreter()

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
                                      self.captures[i]), range(len(self.captures)))):
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
                if not all(map(lambda ex: compiled_re.fullmatch(ex[0]) is not None,
                               self.valid)):
                    continue
                if not all(map(lambda ex: all(map(lambda g: is_int(g) or is_float(g),
                                        compiled_re.fullmatch(ex[0]).groups())), self.valid)):
                    continue
                condition = self._synthesize_conditions_for_captures(regex, sub)
                if condition is not None:
                    return condition, sub
        return None, None

    def _synthesize_conditions_for_captures(self, regex, capture_groups):
        assert len(self.condition_invalid) > 0
        self._cc_enumerator = CaptureConditionsEnumerator(self.interpreter.eval(regex, captures=capture_groups),
                                                          len(capture_groups), self.valid, self.condition_invalid)
        condition_distinguisher = ConditionDistinguisher(regex, capture_groups, self.valid[0][0])

        conditions = []
        while True:
            new_condition = self._cc_enumerator.next()
            if new_condition is not None:
                self._cc_enumerator.update()
                conditions.append(new_condition)
                if len(conditions) > 1:
                    dist_input, keep_if_valid, keep_if_invalid = \
                        condition_distinguisher.distinguish(conditions[0], conditions[1])
                    if not self.auto_interact:
                        conditions = self._interact(dist_input, keep_if_valid, keep_if_invalid)
                    else:
                        conditions = self._auto_distinguish(dist_input, keep_if_valid, keep_if_invalid)
            else:
                if len(conditions) == 0:
                    return None
                else:
                    assert len(conditions) == 1
                    return conditions[0]

    def _interact(self, dist_input, keep_if_valid, keep_if_invalid):
        """ Interact with user to ascertain whether the distinguishing input is valid """
        while True:
            x = input(f'Is "{dist_input}" valid?\n')
            if x.lower().rstrip() in yes_values:
                logger.info(f'"{dist_input}" is {colored("valid", "green")}.')
                self.valid.append([dist_input])
                self._cc_enumerator.add_valid(dist_input)
                return [keep_if_valid]
            elif x.lower().rstrip() in no_values:
                logger.info(f'"{dist_input}" is {colored("conditional invalid", "red")}.')
                self.condition_invalid.append([dist_input])
                self._cc_enumerator.add_conditional_invalid(dist_input)
                return [keep_if_invalid]
            else:
                logger.info(f"Invalid answer {x}! Please answer 'yes' or 'no'.")

    def _auto_distinguish(self, dist_input: str, keep_if_valid: List, keep_if_invalid: List):
        """ Simulate interaction """
        match = re.fullmatch(self.ground_truth_regex, dist_input)
        if match is not None and self._check_conditions(match):
            logger.info(f'Auto: "{dist_input}" is {colored("valid", "green")}.')
            self.valid.append([dist_input])
            self._cc_enumerator.add_valid(dist_input)
            return [keep_if_valid]

        logger.info(f'Auto: "{dist_input}" is {colored("conditional invalid", "red")}.')
        self.condition_invalid.append([dist_input])
        self._cc_enumerator.add_conditional_invalid(dist_input)
        return [keep_if_invalid]

    def _check_conditions(self, match):
        max_group_index = max(map(lambda c: int(c.split(" ")[0].replace("$", "", 1)), self.ground_truth_conditions))
        if len(match.groups()) < max_group_index+1:
            return False
        for condition in self.ground_truth_conditions:
            condition = condition.split(" ")
            group_idx = int(condition[0].replace("$", "", 1))
            operator = condition_operators[condition[1]]
            value = int(condition[2])
            string_value = int(match.groups()[group_idx])
            if not operator(string_value, value):
                return False
        return True
