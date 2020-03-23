import re
import tyrell.spec as spec
from tyrell.common_substrings import find_all_cs
from tyrell.logger import get_logger

logger = get_logger('tyrell.synthesizer')


# TODO: Because different input fields have different types, I must have a different DSL for each input field. To
#  achieve this, I must find a way to return a "set" of DSLs. Perhaps one per field type?
# Idea: return a list of DSLs, where the position in the list corresponds to the position in the types list
class DSLBuilder:

    def __init__(self, type_validations, valid, invalid):
        assert len(valid) > 0
        assert len(type_validations) == len(valid[0])
        assert all(map(lambda l: len(l) == len(valid[0]), valid))
        assert len(invalid) == 0 or all(map(lambda l: len(l) == len(valid[0]), invalid))
        self.types = type_validations
        self.valid = valid
        self.transposed_valid = list(map(list, zip(*valid)))
        self.invalid = invalid
        self.transposed_invalid = list(map(list, zip(*invalid)))
        self.special_chars = {'.', '^', '$', '*', '+', '?', '\\', '|', '(', ')', '{', '}', '[', ']', '"'}

    def build(self):
        dsls = []
        for idx, ty in enumerate(self.types):
            dsls.append(self.build_dsl(ty, self.transposed_valid[idx]))
        return dsls

    def build_dsl(self, val_type, valid):
        dsl = ''
        with open("DSLs/" + re.sub('^is_', '', val_type) + "DSL.tyrell", "r") as dsl_file:
            dsl_base = dsl_file.read()

        if "integer" in val_type:

            dsl += "enum Value {" + ", ".join(map(lambda x: f'"{x}"', self.get_values(int, valid))) + "}\n"

        elif "real" in val_type:
            dsl += "enum Value {" + ", ".join(map(lambda x: f'"{x}"', self.get_values(float, valid))) + "}\n"

        elif "string" in val_type:
            dsl += "enum Value {" + ",".join(map(lambda x: f'"{x}"', self.get_values(len, valid))) + "}\n"
            dsl += "enum Char {" + ",".join(map(lambda x: f'"{x}"', self.get_relevant_chars(valid))) + "}\n"
            dsl += "enum NumCopies {" + ",".join(map(lambda x: f'"{x}"', self.get_num_copies(valid))) + "}\n"

        elif "regex" in val_type:
            dsl += "enum Char {" + ",".join(map(lambda x: f'"{x}"', self.get_relevant_chars(valid))) + "}\n"
            dsl += "enum NumCopies {" + ",".join(map(lambda x: f'"{x}"', self.get_num_copies(valid))) + "}\n"

        logger.debug("\n" + dsl)

        dsl += dsl_base

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

    def get_relevant_chars(self, valid):
        # IDEA: add chars that occur in many examples. Counterargument: I needed to forcefully add a date that did not
        #  contain a 1, and yet a 1 is not a requirement for a date.
        # IDEA: Add individual chars if not all (or almost all) chars occur.
        relevant_chars = set()
        substrings = set()
        char_classes = set()
        letters = set()
        numbers = set()

        substrings.update(find_all_cs(valid))
        for substring in substrings:
            if substring in self.special_chars:
                relevant_chars.add(f"\\{substring}")
            elif substring == "'":
                relevant_chars.add(f'"{substring}"')
            else:
                relevant_chars.add(substring)
        
        # remove substring occurrence from example
        for sub in substrings:
            valid = map(lambda f: f.replace(sub, "", 1), valid)
        for ex in valid:
            for char in ex:
                # This will not work for non-ASCII letters, such as accentuated letters.
                # To counteract this, consider using python's "\w" instead of just the [A-Z] range.
                if 'A' <= char <= 'Z':
                    char_classes.add('[A-Z]')
                    letters.add(char)
                elif 'a' <= char <= 'z':
                    letters.add(char)
                    char_classes.add('[a-z]')
                elif '0' <= char <= '9':
                    numbers.add(char)
                    char_classes.add('[0-9]')
                elif char in self.special_chars:
                    relevant_chars.add(f"\\{char}")
                elif char == "'":
                    relevant_chars.add(f'"{char}"')
                else:
                    relevant_chars.add(char)

        if len(letters) < 5:
            relevant_chars.update(letters)
        if len(numbers) < 5:
            relevant_chars.update(numbers)

        self.update_char_classes(char_classes)
        relevant_chars.update(char_classes)
        return sorted(relevant_chars)

    def get_num_copies(self, valid):
        num_copies = set()

        compressed = valid.copy()

        substrings = set()
        for field in valid:
            substrings.update(find_all_cs(field))

        for ss in substrings:
            compressed = list(map(lambda x: x.replace(ss, '.'), compressed))

        lens = map(len, compressed)
        m = max(lens) + 1
        m = max(m, 3)
        num_copies.update(range(2, m))

        return sorted(num_copies)

    def update_char_classes(self, char_classes):
        if '[0-9]' in char_classes and '[A-Z]' in char_classes:
            char_classes.add('[0-9A-Z]')
        if '[0-9]' in char_classes and '[a-z]' in char_classes:
            char_classes.add('[0-9a-z]')
        if '[A-Z]' in char_classes and '[a-z]' in char_classes:
            char_classes.add('[A-Za-z]')
        if '[0-9]' in char_classes and '[A-Z]' in char_classes and '[a-z]' in char_classes:
            char_classes.add('[0-9A-Za-z]')
