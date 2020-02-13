import re
from LCS import LCSubStr


def get_relevant_chars(examples):
    relevant_chars = set()

    # filter valid examples
    valid = list(filter(lambda x: x.output == True, examples))

    # discard outputs and transpose, i.e., separate by field.
    transposed_valid = list(map(list, zip(*valid)))[0]
    transposed_valid = list(map(list, zip(*transposed_valid)))

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
    return relevant_chars


def build_dsl(type_validation, examples):
    type_validation = type_validation[0]
    dsl = ''
    with open("DSLs/" + re.sub('^is_', '', type_validation) + "DSL.tyrell", "r") as dsl_file:
        dsl_base = dsl_file.read()

    if "integer" in type_validation:
        exs_in = [int(ex.input[0]) for ex in filter(lambda x: x.output == True, examples)]
        values = set()
        values.add(min(exs_in))
        values.add(max(exs_in))
        dsl += "enum Value {" + ", ".join([f'"{x}"' for x in values]) + "}\n"

    elif "real" in type_validation:
        exs_in = [float(ex.input[0]) for ex in filter(lambda x: x.output == True, examples)]
        values = set()
        values.add(min(exs_in))
        values.add(max(exs_in))
        dsl += "enum Value {" + ", ".join([f'"{x}"' for x in values]) + "}\n"


    elif "string" in type_validation:
        exs_in = [len(ex.input[0]) for ex in filter(lambda x: x.output == True, examples)]
        values = set()
        values.add(min(exs_in))
        values.add(max(exs_in))
        dsl += "enum Value {" + ", ".join([f'"{x}"' for x in values]) + "}\n"

        dsl += "enum NumCopies {" + ", ".join([f'"{x}"' for x in [6,4,3,2]]) + "}\n"

        dsl += "enum Char {" + ", ".join([f'"{x}"' for x in get_relevant_chars(examples)]) + "}\n"

    dsl += dsl_base

    return dsl
