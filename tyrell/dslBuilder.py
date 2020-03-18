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
        self.types = type_validations
        self.valid = valid
        self.transposed_valid = list(map(list, zip(*valid)))
        self.invalid = invalid
        self.transposed_invalid = list(map(list, zip(*invalid)))

        self.special_chars = {'.', '^', '$', '*', '+', '?', '\\', '|', '(', ')', '{', '}', '[', ']', '"'}
        self.compute_chars()

    def build(self):
        DSLs = []
        for type in self.types:
            DSLs.append(self.build_dsl(type))

        return DSLs


    def build_dsl(self, val_type):
        dsl = ''
        with open("DSLs/" + re.sub('^is_', '', val_type) + "DSL.tyrell", "r") as dsl_file:
            dsl_base = dsl_file.read()

        if "integer" in val_type:

            dsl += "enum Value {" + ", ".join(map(lambda x: f'"{x}"', self.get_values(int))) + "}\n"

        elif "real" in val_type:
            dsl += "enum Value {" + ", ".join(map(lambda x: f'"{x}"', self.get_values(float))) + "}\n"

        elif "string" in val_type:
            dsl += "enum Value {" + ",".join(map(lambda x: f'"{x}"', self.get_values(len))) + "}\n"
            dsl += "enum Char {" + ",".join(map(lambda x: f'"{x}"', self.relevant_chars)) + "}\n"
            dsl += "enum NumCopies {" + ",".join(map(lambda x: f'"{x}"', self.get_num_copies())) + "}\n"

        dsl += dsl_base

        logger.debug(dsl)

        dsl = spec.parse(dsl)

        return dsl

    def get_values(self, func):
        values_list = list(map(lambda field: map(func, field), self.transposed_valid))
        values = set()
        for field in values_list:
            field = list(field)
            values.add(min(field))
            values.add(max(field))
        return sorted(values)

    def compute_chars(self):
        # IDEA: add chars that occur in many examples. Counterargument: I needed to forcefully add a date that did not
        #  contain a 1, and yet a 1 is not a requirement for a date.
        # IDEA: Add individual chars if not all (or almost all) chars occur.
        relevant_chars = set()
        char_classes = set()
        letters = set()
        numbers = set()
        substrings = set()

        for field in self.transposed_valid:
            substrings.update(find_all_cs(field))
            relevant_chars.update(substrings)
            # remove substring occurrence from example
            for sub in substrings:
                field = map(lambda f: f.replace(sub, "", 1), field)
            for ex in field:
                for char in ex:
                    # This will not work for non-ASCII letters, such as accentuated letters.
                    # To counteract this, consider using python's "\w" instead of just the [A-Z] range.
                    if 'A' <= char <= 'Z':
                        relevant_chars.add('[A-Z]')
                        char_classes.add('[A-Z]')
                        letters.add(char)
                        # if a char occurs in all strings, add it too.
                        # This is stupid, because then it will be a substring
                        # if all([char in ex for ex in field]):
                        #    relevant_chars.add(char)
                        if '[a-z]' in relevant_chars:
                            relevant_chars.add('[A-Za-z]')
                            char_classes.add('[A-Za-z]')
                        if '[0-9]' in relevant_chars:
                            relevant_chars.add('[0-9A-Z]')
                            char_classes.add('[0-9A-Z]')
                        if '[a-z]' in relevant_chars and '[0-9]' in relevant_chars:
                            relevant_chars.add('[0-9A-Za-z]')
                            char_classes.add('[0-9A-Za-z]')
                    elif 'a' <= char <= 'z':
                        letters.add(char)
                        relevant_chars.add('[a-z]')
                        char_classes.add('[a-z]')
                        # if all([char in s for s in field]):
                        #     relevant_chars.add(char)
                        if '[A-Z]' in relevant_chars:
                            relevant_chars.add('[A-Za-z]')
                            char_classes.add('[A-Za-z]')
                        if '[0-9]' in relevant_chars:
                            relevant_chars.add('[0-9a-z]')
                            char_classes.add('[0-9a-z]')
                        if '[A-Z]' in relevant_chars and '[0-9]' in relevant_chars:
                            relevant_chars.add('[0-9A-Za-z]')
                            char_classes.add('[0-9A-Za-z]')
                    elif '0' <= char <= '9':
                        numbers.add(char)
                        relevant_chars.add('[0-9]')
                        char_classes.add('[0-9]')
                        if '[A-Z]' in relevant_chars:
                            relevant_chars.add('[0-9A-Z]')
                            char_classes.add('[0-9A-Z]')
                        if '[a-z]' in relevant_chars:
                            relevant_chars.add('[0-9a-z]')
                            char_classes.add('[0-9a-z]')
                        if '[a-z]' in relevant_chars and '[A-Z]' in relevant_chars:
                            relevant_chars.add('[0-9A-Za-z]')
                            char_classes.add('[0-9A-Za-z]')
                        # if all([(char in s) for s in field]):
                        #     relevant_chars.add(char)
                    elif char in self.special_chars:
                        relevant_chars.add(f"\{char}")
                    elif char == "'":
                        relevant_chars.add(f'"{char}"')
                    else:
                        relevant_chars.add(char)
        self.relevant_chars = sorted(relevant_chars)
        self.numbers = numbers
        self.letters = letters
        self.substrings = substrings
        self.char_classes = char_classes


    def get_num_copies(self):
        num_copies = set()

        compressed = self.transposed_valid[0].copy()
        for ss in self.substrings:
            compressed = list(map(lambda x: x.replace(ss, '.'), compressed))


        lens = map(len, compressed)
        m = max(lens)
        num_copies.update(range(2, m))

        if 1 in num_copies: num_copies.remove(1) # 1 makes no sense for this operation
        return sorted(num_copies)



