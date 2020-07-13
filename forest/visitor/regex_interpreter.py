import re
from typing import Any, Tuple, Union

from .post_order import PostOrderInterpreter
from ..dsl import Node


class RegexInterpreter(PostOrderInterpreter):
    def __init__(self):
        super().__init__()
        self.precedences = {}
        self.captures = []

    def eval(self, regex: Union[Node, Tuple], inputs=None, captures=None) -> Any:
        """
        Interpret the Given AST in post-order. Assumes the existence of `eval_XXX` method
        where `XXX` is the name of a function defined in the DSL.
        """
        if isinstance(regex, Tuple):
            if len(regex) > 1:
                captures = regex[1]
            else:
                captures = None
            regex = regex[0]
        if captures is None:
            captures = []
        self.captures = captures
        return PostOrderInterpreter.eval(self, regex, inputs)

    def eval_Input(self, v):
        return v

    def eval_String(self, v):
        return v

    def eval_Number(self, v) -> float:
        return float(v)

    def eval_Value(self, v):
        return float(v)

    def eval_RegexLit(self, v):
        return v

    def eval_RangeLit(self, v):
        s = v.split(',')
        if len(s) == 2:
            return int(s[0]), int(s[1])
        else:  # sketches
            return str(v)

    def eval_Regex(self, v):
        return v

    def eval_Bool(self, v):
        return v

    def eval_re(self, node, args):
        self.precedences[node.production.id] = 5
        ret = f'{args[0]}'
        if any(map(lambda cap: node in cap, self.captures)):
            for cap in self.captures:
                if node == cap[0]:
                    ret = '(' + ret
                if node == cap[-1]:
                    ret = ret + ')'
        return ret

    def eval_unary_operator(self, arg, node, symbol):
        child_id = node.children[0].production.id
        child_prec = self.precedences[child_id]
        if child_prec >= self.precedences[node.production.id]:
            ret = f'{arg[0]}{symbol}'
        else:
            ret = f'(?:{arg[0]}){symbol}'
        if any(map(lambda cap: node in cap, self.captures)):
            for cap in self.captures:
                if node == cap[0]:
                    ret = '(' + ret
                if node == cap[-1]:
                    ret = ret + ')'
        return ret

    def eval_nary_operator(self, args, node, sep):
        children_str = []
        for child_idx in range(len(node.children)):
            child_id = node.children[child_idx].production.id
            child_prec = self.precedences[child_id]
            if child_prec >= self.precedences[node.production.id]:
                ch = f'{args[child_idx]}'
            else:
                ch = f'(?:{args[child_idx]})'

            children_str.append(f'{ch}')
        children_str = sep.join(children_str)
        if any(map(lambda cap: node in cap, self.captures)):
            for cap in self.captures:
                if node == cap[0]:
                    children_str = '(' + children_str
                if node == cap[-1]:
                    children_str = children_str + ')'
        return children_str

    def eval_kleene(self, node, args):
        self.precedences[node.production.id] = 4
        return self.eval_unary_operator(args, node, '*')

    def eval_option(self, node, args):
        self.precedences[node.production.id] = 4
        return self.eval_unary_operator(args, node, '?')

    def eval_posit(self, node, args):
        self.precedences[node.production.id] = 4
        return self.eval_unary_operator(args, node, '+')

    def eval_range(self, node, args):
        self.precedences[node.production.id] = 3
        child_id = node.children[0].production.id
        child_prec = self.precedences[child_id]
        range_vals = args[1]
        if not len(range_vals) == 2:
            range_vals_str = range_vals
        elif range_vals[0] == range_vals[1]:
            range_vals_str = str(range_vals[0])
        else:
            range_vals_str = f"{range_vals[0]},{range_vals[1]}"
        if child_prec >= self.precedences[node.production.id]:
            ret = f'{args[0]}{{{range_vals_str}}}'
        else:
            ret = f'(?:{args[0]}){{{range_vals_str}}}'
        if any(map(lambda cap: node in cap, self.captures)):
            for cap in self.captures:
                if node == cap[0]:
                    ret = '(' + ret
                if node == cap[-1]:
                    ret = ret + ')'
        return ret

    def eval_concat(self, node, args):
        self.precedences[node.production.id] = 2
        return self.eval_nary_operator(args, node, '')

    def eval_union(self, node, args):
        self.precedences[node.production.id] = 1
        return self.eval_nary_operator(args, node, '|')

    def eval_match(self, node, args):
        match = re.fullmatch(args[0], args[1])
        return match is not None
