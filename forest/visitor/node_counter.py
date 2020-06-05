from forest.dsl import Node
from .post_order import PostOrderInterpreter


class NodeCounter(PostOrderInterpreter):
    # */+/? concat |
    # {"kleene":3, "copies":3, "posit":3, "option":3, "concat":2, "union":1}
    def __init__(self):
        super().__init__()

    def eval_Input(self, v):
        return 0

    def eval_Number(self, v):
        return 0

    def eval_Bool(self, v):
        return 0

    def eval_Value(self, v):
        return 0

    def eval_RegexLit(self, v):
        return 0

    def eval_RangeLit(self, v):
        return 1

    def eval_conj(self, node: Node, args) -> str:
        """Bool -> Bool, Bool;"""
        return 1 + sum(args)

    def eval_number(self, node, args) -> str:
        """Number -> Input;"""
        return 1 + sum(args)

    def eval_is_int(self, node, args) -> str:
        '''Bool -> Input;'''
        return 1 + sum(args)

    def eval_is_real(self, node, args) -> str:
        '''Bool -> Input;'''
        return 1 + sum(args)

    def eval_is_string(self, node, args) -> str:
        '''Bool -> Input;'''
        return 1 + sum(args)

    def eval_string(self, node, args) -> str:
        '''String -> Input;'''
        return 1 + sum(args)

    def eval_len(self, node, args) -> str:
        '''Number -> String;'''
        return 1 + sum(args)

    def eval_le(self, node, args) -> str:
        ''''Bool -> Number, Number;'''
        return 1 + sum(args)

    def eval_ge(self, node, args) -> str:
        '''Bool -> Number, Number;'''
        return args[0] + " >= " + args[1]

    def eval_re(self, node, args):
        return 1 + sum(args)

    def eval_kleene(self, node: Node, args):
        return 1 + sum(args)

    def eval_option(self, node, args):
        return 1 + sum(args)

    def eval_posit(self, node, args):
        return 1 + sum(args)

    def eval_range(self, node, args):
        return 1 + sum(args)

    def eval_concat(self, node, args):
        return 1 + sum(args)

    def eval_union(self, node, args):
        return 1 + sum(args)

    def eval_match(self, node, args):
        return sum(args)
