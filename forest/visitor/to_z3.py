from typing import Union, Tuple, Any

import z3

from .post_order import PostOrderInterpreter
from ..dsl import Node


class ToZ3(PostOrderInterpreter):
    """
    Returns a z3 regular expression that corresponds to the argument of the match() operation in the program
    """

    def __init__(self):
        super().__init__()

    def eval(self, program: Union[Node, Tuple], inputs=None) -> Any:
        """
        Interpret the Given AST in post-order. Assumes the existence of `eval_XXX` method
        where `XXX` is the name of a function defined in the DSL.
        """
        if isinstance(program, Tuple):
            program = program[0]
        return PostOrderInterpreter.eval(self, program, inputs)

    def eval_Input(self, v):
        return None

    def eval_String(self, v):
        return None

    def eval_Number(self, v):
        return None

    def eval_Value(self, v):
        return None

    def eval_Regex(self, v):
        return v

    def eval_Bool(self, v):
        return v

    def eval_RegexLit(self, c: str):
        if c.startswith('\\'):
            c = c.replace("\\", '', 1)
            # c = re.sub(r'\\(.)', r'\1', c)
        return c

    def eval_RangeLit(self, v):
        s = v.split(',')
        assert len(s) == 2
        return (int(s[0]), int(s[1]))

    def eval_conj(self, node, args) -> bool:
        return args[0] if args[0] is not None else args[1]

    def eval_number(self, node, args):
        return None

    def eval_len(self, node, args):
        return None

    def eval_le(self, node, args):
        return None

    def eval_ge(self, node, args):
        return None

    def eval_re(self, node, args):
        ranges = []
        c = args[0]
        if "0-9" in c:
            ranges.append(z3.Range('0', '9'))
        if "a-z" in c:
            ranges.append(z3.Range('a', 'z'))
        if "A-Z" in c:
            ranges.append(z3.Range('A', 'Z'))

        if len(ranges) == 1:
            return ranges[0]
        elif len(ranges) > 1:
            return z3.Union(ranges)
        else:
            return z3.Re(c)

    def eval_kleene(self, node, args):
        return z3.Star(args[0])

    def eval_option(self, node, args):
        return z3.Option(args[0])

    def eval_posit(self, node, args):
        return z3.Plus(args[0])

    def eval_range(self, node, args):
        range_vals = args[1]
        assert len(range_vals) == 2
        return z3.Loop(args[0], range_vals[0], range_vals[1])

    def eval_concat(self, node, args):
        if len(args) == 1:
            return args[0]
        return z3.Concat(args)

    def eval_union(self, node, args):
        if len(args) == 1:
            return args[0]
        return z3.Union(args)

    def eval_match(self, node, args):
        return args[0]
