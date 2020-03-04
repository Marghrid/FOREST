import re
from .post_order import PostOrderInterpreter


class ValidationInterpreter(PostOrderInterpreter):
    def __init__(self):
        super().__init__()
        self.precedences = {}

    def check_integer(self, arg):
        if isinstance(arg, int):
            return True
        try:
            int(arg)
            return True
        except (TypeError, ValueError):
            return False

    def check_real(self, arg):
        if self.check_integer(arg): return False
        if isinstance(arg, float):
            return True
        try:
            float(arg)
            return True
        except (TypeError, ValueError):
            return False

    def eval_Input(self, v):
        return v

    def eval_String(self, v):
        return v

    def eval_Number(self, v) -> float:
        return float(v)

    def eval_Value(self, v):
        return float(v)

    def eval_Char(self, v):
        return v

    def eval_conj(self, node, args) -> bool:
        '''Bool -> Bool, Bool;'''
        return args[0] and args[1]

    def eval_number(self, node, args) -> float:
        return float(args[0])

    def eval_len(self, node, args) -> int:
        return len(args[0])

    def eval_le(self, node, args) -> bool:
        return args[0] <= args[1]

    def eval_ge(self, node, args) -> bool:
        return args[0] >= args[1]

    def eval_Regex(self, v):
        return v

    def eval_Bool(self, v):
        return v

    def eval_re(self, node, args):
        self.precedences[node.production.id] = 4
        return fr'{args[0]}'

    def eval_kleene(self, node, args):
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
        match = re.fullmatch(args[0], args[1])
        return match is not None

    def eval_partial_match(self, node, args):
        match = re.match(args[0], args[1])
        return match is not None
