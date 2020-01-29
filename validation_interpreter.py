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

    def eval_conj(self, node, args) -> bool:
        '''Bool -> Bool, Bool;'''
        return args[0] and args[1]

    def eval_number(self, node, args) -> float:
        '''Number -> Input;'''
        return float(args[0])

    def eval_is_int(self, node, args) -> bool:
        '''Bool -> Input;'''
        return self.check_integer(args[0])

    def eval_is_real(self, node, args) -> bool:
        '''Bool -> Input;'''
        return self.check_real(args[0])

    def eval_is_string(self, node, args) -> bool:
        '''Bool -> Input;'''
        return isinstance(args[0], str) and self.check_integer(args[0]) and not self.check_real(args[0])

    def eval_string(self, node, args) -> str:
        '''String -> Input;'''
        return args[0]

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

    def apply_is_number(self, val) -> bool:
        return self.check_integer(val) or self.check_real(val)


def check_integer(arg):
    if isinstance(arg, int):
        return True
    try:
        int(arg)
        return True
    except (TypeError, ValueError):
        return False


def check_real(arg):
    if check_integer(arg): return False
    if isinstance(arg, float):
        return True
    try:
        float(arg)
        return True
    except (TypeError, ValueError):
        return False


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

    def apply_is_number(self, val) -> bool:
        return check_integer(val) or check_real(val)
