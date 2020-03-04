from tyrell.dsl import Node
from .post_order import PostOrderInterpreter


class ValidationPrinter(PostOrderInterpreter):
    # */+/? concat |
    # {"kleene":3, "copies":3, "posit":3, "option":3, "concat":2, "union":1}
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
        self.precedences[node.production.id] = 4
        return args[0]

    def eval_kleene(self, node: Node, args):
        self.precedences[node.production.id] = 3
        child_id = node.children[0].production.id
        child_prec = self.precedences[child_id]
        if child_prec >= self.precedences[node.production.id]:
            return f'{args[0]}*'
        else:
            return f'({args[0]})*'

    def eval_option(self, node, args):
        self.precedences[node.production.id] = 3
        child_id = node.children[0].production.id
        child_prec = self.precedences[child_id]
        if child_prec >= self.precedences[node.production.id]:
            return f'{args[0]}?'
        else:
            return f'({args[0]})?'

    def eval_posit(self, node, args):
        self.precedences[node.production.id] = 3
        child_id = node.children[0].production.id
        child_prec = self.precedences[child_id]
        if child_prec >= self.precedences[node.production.id]:
            return f'{args[0]}+'
        else:
            return f'({args[0]})+'

    def eval_copies(self, node, args):
        self.precedences[node.production.id] = 3
        child_id = node.children[0].production.id
        child_prec = self.precedences[child_id]
        if child_prec >= self.precedences[node.production.id]:
            return f'{args[0]}{{{args[1]}}}'
        else:
            return f'({args[0]}){{{args[1]}}}'

    def eval_concat(self, node, args):
        self.precedences[node.production.id] = 2
        child_id = node.children[0].production.id
        child_prec = self.precedences[child_id]
        if child_prec >= self.precedences[node.production.id]:
            ch0 = f'{args[0]}'
        else:
            ch0 = f'({args[0]})'

        child_id = node.children[1].production.id
        child_prec = self.precedences[child_id]
        if child_prec >= self.precedences[node.production.id]:
            ch1 = f'{args[1]}'
        else:
            ch1 = f'({args[1]})'
        return f'{ch0}{ch1}'

    def eval_union(self, node, args):
        self.precedences[node.production.id] = 1
        child_id = node.children[0].production.id
        child_prec = self.precedences[child_id]
        if child_prec >= self.precedences[node.production.id]:
            ch0 = f'{args[0]}'
        else:
            ch0 = f'({args[0]}) '

        child_id = node.children[1].production.id
        child_prec = self.precedences[child_id]
        if child_prec >= self.precedences[node.production.id]:
            ch1 = f'{args[1]}'
        else:
            ch1 = f' ({args[1]})'
        return f'{ch0}|{ch1}'




    def eval_match(self, node, args):
        return f"match({args[0]}, {args[1]})"

    def eval_partial_match(self, node, args):
        return f"partial_match({args[0]}, {args[1]})"