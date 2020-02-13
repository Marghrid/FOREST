import re
import sys
from tyrell.interpreter import PostOrderInterpreter


class ValidationInterpreter(PostOrderInterpreter):
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

    def eval_Regex(self, v):
        return v

    def eval_Input(self, v):
        return v

    def eval_String(self, v):
        return v

    def eval_Number(self, v) -> float:
        return float(v)

    def eval_Bool(self, v):
        return v

    def eval_Value(self, v):
        return float(v)

    def eval_Char(self, v):
        return v

    def eval_conj(self, node, args) -> bool:
        '''Bool -> Bool, Bool;'''
        return args[0] and args[1]

    def eval_number(self, node, args) -> float:
        '''Number -> Input;'''
        return float(args[0])

    def eval_len(self, node, args) -> int:
        '''Number -> String;'''
        return len(args[0])

    def eval_le(self, node, args) -> bool:
        ''''Bool -> Number, Number;'''
        # print("le", args[0], args[1], args[0] <= args[1], file=sys.stderr)
        return args[0] <= args[1]

    def eval_ge(self, node, args) -> bool:
        '''Bool -> Number, Number;'''
        # print("ge", args[0], args[1], args[0] >= args[1], file=sys.stderr)
        return args[0] >= args[1]

    def eval_Regex(self, v):
        return int(v)

    def eval_Bool(self, v):
        return int(v)

    def eval_re(self, node, args):
        return fr'{args[0]}'

    def eval_kleene(self, node, args):
        if len(args[0]) == 1: return fr'{args[0]}*'
        return fr'({args[0]})*'

    def eval_copies(self, node, args):
        if len(args[0]) == 1: return fr'{args[0]}{{{args[1]}}}'
        return fr'({args[0]}){{{args[1]}}}'

    def eval_concat(self, node, args):
        return fr'{args[0]}{args[1]}'

    def eval_union(self, node, args):
        if len(args[0]) == 1:
            h0 = fr'{args[0]}'
        else:
            h0 = fr'({args[0]})'
        if len(args[1]) == 1:
            h1 = fr'{args[1]}'
        else:
            h1 = fr'({args[1]})'
        return h0 + '|' + h1

    def eval_interr(self, node, args):
        if len(args[0]) == 1: return fr'{args[0]}?'
        return fr'({args[0]})?'

    def eval_posit(self, node, args):
        if len(args[0]) == 1: return fr'{args[0]}+'
        return fr'({args[0]})+'

    def eval_match(self, node, args):
        match = re.fullmatch(args[0], args[1])
        return match is not None

    def eval_partial_match(self, node, args):
        match = re.match(args[0], args[1])
        return match is not None
