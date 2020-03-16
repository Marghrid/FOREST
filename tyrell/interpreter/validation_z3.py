import z3

from .post_order import PostOrderInterpreter


class Validation_z3(PostOrderInterpreter):
    """
    Returns a z3 regular expression that corresponds to the argument of the match() operation in the program
    """

    def __init__(self):
        super().__init__()

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

    def eval_Char(self, c):
        return c

    def eval_NumCopies(self, v):
        return int(v)

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

    def eval_copies(self, node, args):
        num_copies = args[1]
        return z3.Loop(args[0], num_copies, num_copies)

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
