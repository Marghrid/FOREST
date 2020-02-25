import re
import tyrell.spec as spec
from LCS import LCSubStr


def get_values(exs_in):
    values = set()
    for field in exs_in:
        field = list(field)
        values.add(min(field))
        values.add(max(field))
    return sorted(values)


def get_relevant_chars(valid_examples):
    relevant_chars = set()

    # discard outputs and transpose, i.e., separate by field.
    transposed_valid = list(map(list, zip(*valid_examples)))

    for field in transposed_valid:
        substrings = LCSubStr(field)
        relevant_chars.update(substrings)
        for sub in substrings:
            field = [field_in.replace(sub, "", 1) for field_in in field]
        for ex in field:
            for char in ex:
                if 'A' <= char <= 'Z':
                    relevant_chars.add('[A-Z]')
                    if all([char in s for s in field]):
                        relevant_chars.add(char)
                    if '[a-z]' in relevant_chars:
                        relevant_chars.add('[A-Za-z]')
                elif 'a' <= char <= 'z':
                    relevant_chars.add('[a-z]')
                    if all([char in s for s in field]):
                        relevant_chars.add(char)
                    if '[A-Z]' in relevant_chars:
                        relevant_chars.add('[A-Za-z]')
                elif '0' <= char <= '9':
                    relevant_chars.add('[0-9]')
                    if all([(char in s) for s in field]):
                        relevant_chars.add(char)
                else:
                    relevant_chars.add(char)
    return sorted(relevant_chars)


# TODO: Should DSL be built using only valid examples?
def build_dsl(type_validation, valid, invalid):
    type_validation = type_validation[0]
    transposed_valid = list(map(list, zip(*valid)))
    dsl = ''
    with open("DSLs/" + re.sub('^is_', '', type_validation) + "DSL.tyrell", "r") as dsl_file:
        dsl_base = dsl_file.read()

    if "integer" in type_validation:
        exs_in = list(map(lambda field : map(int, field), transposed_valid))
        dsl += "enum Value {" + ", ".join([f'"{x}"' for x in get_values(exs_in)]) + "}\n"

    elif "real" in type_validation:
        exs_in = list(map(lambda field : map(float, field), transposed_valid))
        dsl += "enum Value {" + ", ".join([f'"{x}"' for x in get_values(exs_in)]) + "}\n"

    elif "string" in type_validation:
        exs_in = list(map(lambda field : map(len, field), transposed_valid))
        dsl += "enum Value {" + ",".join([f'"{x}"' for x in get_values(exs_in)]) + "}\n"
        dsl += "enum NumCopies {" + ",".join([f'"{x}"' for x in [6, 4, 3, 2]]) + "}\n"
        dsl += "enum Char {" + ",".join([f'"{x}"' for x in get_relevant_chars(valid)]) + "}\n"

    dsl += dsl_base

    dsl = spec.parse(dsl)

    return dsl
