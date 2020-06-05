from forest.dsl import Node
from .post_order import PostOrderInterpreter


class ValidationPrinter(PostOrderInterpreter):
    # */+/? concat |
    # {"kleene":3, "range":3, "posit":3, "option":3, "concat":2, "union":1}
    def __init__(self):
        super().__init__()
        self.precedences = {}

    def eval_Regex(self, v):
        return v

    def eval_Input(self, v):
        return v

    def eval_Number(self, v) -> str:
        return v

    def eval_Bool(self, v):
        return v

    def eval_Value(self, v):
        return v

    def eval_RangeVal(self, v):
        s = v.split(',')
        assert len(s) == 2
        return int(s[0]), int(s[1])

    def eval_conj(self, node: Node, args) -> str:
        """Bool -> Bool, Bool;"""
        return args[0] + " /\\ " + args[1]

    def eval_number(self, node, args) -> str:
        """Number -> Input;"""
        return args[0]

    def eval_is_int(self, node, args) -> str:
        '''Bool -> Input;'''
        return "is int(" + args[0] + ")"

    def eval_is_real(self, node, args) -> str:
        '''Bool -> Input;'''
        return "is real(" + args[0] + ")"

    def eval_is_string(self, node, args) -> str:
        '''Bool -> Input;'''
        return "is string(" + args[0] + ")"

    def eval_string(self, node, args) -> str:
        '''String -> Input;'''
        return args[0]

    def eval_len(self, node, args) -> str:
        '''Number -> String;'''
        return "len(" + args[0] + ")"

    def eval_le(self, node, args) -> str:
        ''''Bool -> Number, Number;'''
        return args[0] + " <= " + args[1]

    def eval_ge(self, node, args) -> str:
        '''Bool -> Number, Number;'''
        return args[0] + " >= " + args[1]

    def eval_re(self, node, args):
        self.precedences[node.production.id] = 5
        if len(args[0]) == 1 or '[' in args[0]:
            return args[0]
        else:
            return fr'({args[0]})'

    def eval_unary_operator(self, args, node, symbol):
        child_id = node.children[0].production.id
        child_prec = self.precedences[child_id]
        if child_prec >= self.precedences[node.production.id]:
            return f'{args[0]}{symbol}'
        else:
            return f'({args[0]}){symbol}'

    def eval_nary_operator(self, args, node, sep):
        children_str = []
        for child_idx in range(len(node.children)):
            child_id = node.children[child_idx].production.id
            child_prec = self.precedences[child_id]
            if child_prec >= self.precedences[node.production.id]:
                ch = f'{args[child_idx]}'
            else:
                ch = f'({args[child_idx]})'

            children_str.append(f'{ch}')
        children_str = sep.join(children_str)
        return children_str

    def eval_kleene(self, node: Node, args):
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
        assert len(range_vals) == 2
        if range_vals[0] == range_vals[1]:
            range_vals_str = str(range_vals[0])
        else:
            range_vals_str = f"{range_vals[0]},{range_vals[1]}"
        if child_prec >= self.precedences[node.production.id]:
            return f'{args[0]}{{{range_vals_str}}}'
        else:
            return f'({args[0]}){{{range_vals_str}}}'

    def eval_concat(self, node, args):
        self.precedences[node.production.id] = 2
        return self.eval_nary_operator(args, node, '')

    def eval_union(self, node, args):
        self.precedences[node.production.id] = 1
        return self.eval_nary_operator(args, node, '|')

    def eval_match(self, node, args):
        return f"match({args[0]}, {args[1]})"

    def eval_partial_match(self, node, args):
        return f"partial_match({args[0]}, {args[1]})"
