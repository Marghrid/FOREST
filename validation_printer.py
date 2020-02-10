from tyrell.interpreter import PostOrderInterpreter


class ValidationPrinter(PostOrderInterpreter):

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

    def eval_conj(self, node, args) -> str:
        '''Bool -> Bool, Bool;'''
        return args[0] + " /\\ " + args[1]

    def eval_number(self, node, args) -> str:
        '''Number -> Input;'''
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
        # print("le", args[0], args[1], args[0] <= args[1], file=sys.stderr)
        return args[0] + " <= " + args[1]

    def eval_ge(self, node, args) -> str:
        '''Bool -> Number, Number;'''
        # print("ge", args[0], args[1], args[0] >= args[1], file=sys.stderr)
        return args[0] + " >= " + args[1]

    def eval_re(self, node, args):
        return args[0]

    def eval_kleene(self, node, args):
        if len(args[0]) == 1: return fr'{args[0]}*'
        return f'({args[0]})*'

    def eval_concat(self, node, args):
        return f'{args[0]}{args[1]}'

    def eval_union(self, node, args):
        if len(args[0]) == 1:
            h0 = f'{args[0]}'
        else:
            h0 = f'({args[0]})'
        if len(args[1]) == 1:
            h1 = f'{args[1]}'
        else:
            h1 = f'({args[1]})'
        return h0 + '|' + h1

    def eval_interr(self, node, args):
        if len(args[0]) == 1: return fr'{args[0]}?'
        return f'({args[0]})?'

    def eval_posit(self, node, args):
        if len(args[0]) == 1: return fr'{args[0]}+'
        return f'({args[0]})+'

    def eval_match(self, node, args):
        return f"match({args[0]}, {args[1]})"