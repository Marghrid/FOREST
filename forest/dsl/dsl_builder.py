import re

import forest.spec as spec
from forest.logger import get_logger
from forest.utils import transpose, find_all_cs

logger = get_logger('forest')


class DSLBuilder:

    def __init__(self, type_validations, valid, invalid, sketches=False):
        assert len(valid) > 0
        # assert len(type_validations) == len(valid[0])
        assert all(map(lambda l: len(l) == len(valid[0]), valid))
        assert len(invalid) == 0 or all(map(lambda l: len(l) <= len(valid[0]), invalid))
        self.types = type_validations
        self.valid = valid
        self.transposed_valid = transpose(valid)
        self.invalid = invalid
        self.transposed_invalid = transpose(invalid)
        self.sketches = sketches
        self.special_chars = {'.', '^', '$', '*', '+', '?', '\\', '|', '(', ')',
                              '{', '}', '[', ']', '"'}

    def build(self):
        dsls = []
        if not self.sketches:
            for idx, ty in enumerate(self.types):
                dsls.append(self.build_dsl(ty, self.transposed_valid[idx]))
        else:
            for idx, ty in enumerate(self.types):
                dsls.append(self.build_sketch_dsl(ty, self.transposed_valid[idx]))
        return dsls

    def build_sketch_dsl(self, val_type, valid):
        dsl = ''
        filename = "forest/dsl/" + re.sub('^is_', '', val_type) + "DSL.tyrell"
        with open(filename, "r") as dsl_file:
            dsl_base = dsl_file.read()
        if "regex" in val_type:
            dsl += 'enum RegexLit {"hole"}\n'
            dsl += 'enum RangeLit {"hole"}\n'
        else:
            logger.error(f"Unknown type validation: {val_type}.")

        dsl += dsl_base
        dsl += self._regex_operators()
        dsl += self._range_operator()
        dsl += self._predicates()

        logger.debug("\n" + dsl)
        dsl = spec.parse(dsl)
        return dsl

    def build_dsl(self, val_type, valid):
        dsl = ''
        range_operator = False
        super_simple_dsl = False
        filename = "forest/dsl/" + val_type + "DSL.tyrell"
        with open(filename, "r") as dsl_file:
            dsl_base = dsl_file.read()

        if "regex" in val_type:
            regexlits = self.get_regexlits(valid)
            dsl += "enum RegexLit {" + ",".join(
                map(lambda x: f'"{x}"', regexlits)) + "}\n"
            if len(regexlits) == 1 and \
                    all(map(lambda x: re.fullmatch(regexlits[0], x) is not None, valid)):
                super_simple_dsl = True
            range_values = self.get_rangelits(valid)
            if len(range_values) > 0:
                range_operator = True
                dsl += "enum RangeLit {" + \
                       ",".join(map(lambda x: f'"{x}"', range_values)) + "}\n"
        else:
            logger.error(f"Unknown type validation: {val_type}.")

        dsl += dsl_base
        if not super_simple_dsl:
            dsl += self._regex_operators()
            if range_operator:
                dsl += self._range_operator()
        if not super_simple_dsl:
            dsl += self._predicates()

        logger.debug("\n" + dsl)

        dsl = spec.parse(dsl)

        return dsl

    def get_values(self, func, valid):
        values_list = list(map(lambda f: map(func, f), valid))
        values = set()
        for field in values_list:
            field = list(field)
            values.add(min(field))
            values.add(max(field))
        return sorted(values)

    def get_regexlits(self, valid):
        regexlits = set()
        substrings = set()
        char_classes = set()
        letters = set()
        numbers = set()

        substrings.update(find_all_cs(valid))
        for substring in substrings:
            if substring in self.special_chars:
                regexlits.add(fr"\{substring}")
            elif substring == "'":
                regexlits.add(f'{substring}')
            else:
                regexlits.add(substring)

        # remove substring occurrence from example
        for sub in substrings:
            valid = map(lambda f: f.replace(sub, "", 1), valid)
        for ex in valid:
            for char in ex:
                # This will not work for non-ASCII letters, such as accentuated
                # letters. To counteract this, consider using python's "\w" instead of
                # just the [A-Z] range.
                if 'A' <= char <= 'Z':
                    char_classes.add('[A-Z]')
                    letters.add(char)
                    if 'A' <= char <= 'F':
                        char_classes.add('[A-F]')
                elif 'a' <= char <= 'z':
                    letters.add(char)
                    char_classes.add('[a-z]')
                    if 'a' <= char <= 'f':
                        char_classes.add('[a-f]')
                elif '0' <= char <= '9':
                    numbers.add(char)
                    char_classes.add('[0-9]')
                elif char in self.special_chars:
                    regexlits.add(fr"\{char}")
                elif char == "'":
                    regexlits.add(f'{char}')
                else:
                    regexlits.add(char)

        if len(letters) < 5:
            regexlits.update(letters)
        if len(numbers) < 5:
            regexlits.update(numbers)

        self.update_char_classes(char_classes)
        regexlits.update(char_classes)
        return sorted(regexlits)

    def get_rangelits(self, valid):
        compressed = valid.copy()

        substrings = set()
        for field in valid:
            substrings.update(find_all_cs(field))

        for ss in substrings:
            compressed = list(map(lambda x: x.replace(ss, '.'), compressed))

        max_l = max(map(len, compressed))
        # m = max(m, 3)

        range_vals = []
        for j in range(2, max_l + 1):
            for i in range(0, j + 1):
                range_vals.append(f'{i},{j}')
        return range_vals

    def update_char_classes(self, char_classes):
        if '[0-9]' in char_classes and '[A-Z]' in char_classes:
            char_classes.add('[0-9A-Z]')
        if '[A-F]' in char_classes:
            if '[0-9]' in char_classes:
                char_classes.add('[0-9A-F]')
            else:
                char_classes.remove('[A-F]')
        if '[a-f]' in char_classes:
            if '[0-9]' in char_classes:
                char_classes.add('[0-9a-f]')
            else:
                char_classes.remove('[a-f]')
        if '[A-F]' in char_classes and '[a-f]' in char_classes and '[0-9]' in char_classes:
            char_classes.add('[0-9A-Fa-f]')
        if '[0-9]' in char_classes and '[a-z]' in char_classes:
            char_classes.add('[0-9a-z]')
        if '[A-Z]' in char_classes and '[a-z]' in char_classes:
            char_classes.add('[A-Za-z]')
        if '[0-9]' in char_classes and '[A-Z]' in char_classes and '[a-z]' in char_classes:
            char_classes.add('[0-9A-Za-z]')

    def _range_operator(self):
        return "func range: Regex -> Regex, RangeLit;\n" \
               "predicate is_not_parent(range, range);\n" \
               "predicate is_not_parent(range, kleene);\n" \
               "predicate is_not_parent(range, posit);\n" \
               "predicate is_not_parent(range, option);\n"

    def _predicates(self):
        return "# predicate is_commutative(union);\n" \
               "predicate is_not_parent(kleene, kleene);\n" \
               "predicate is_not_parent(option, option);\n" \
               "predicate is_not_parent(posit,  posit);\n" \
               "predicate is_not_parent(kleene, posit);\n" \
               "predicate is_not_parent(kleene, option);\n" \
               "predicate is_not_parent(posit, kleene);\n" \
               "predicate is_not_parent(posit, option);\n" \
               "predicate is_not_parent(option, kleene);\n" \
               "predicate is_not_parent(option, posit);\n"

    def _regex_operators(self):
        return 'func concat: Regex -> Regex, Regex;\n' \
               'func union:  Regex -> Regex, Regex;\n' \
               'func kleene: Regex s -> Regex r;\n' \
               'func posit:  Regex s -> Regex r;\n' \
               'func option: Regex s -> Regex r;\n'
