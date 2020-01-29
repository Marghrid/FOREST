import re


def build_dsl(type_validation, examples):
    type_validation = type_validation[0]
    dsl = ''
    with open( "DSLs/" + re.sub('^is_', '', type_validation) + "DSL.tyrell", "r") as dsl_file:
        dsl_base =  dsl_file.read()

    if "integer" in type_validation:
        dsl += "enum Value {"
        exs_in = [int(ex.input[0]) for ex in filter(lambda x: x.output == True, examples)]
        min_in, max_in = min(exs_in), max(exs_in)
        dsl += f'"{str(min_in)}", "{str(max_in)}"'
        dsl += "}\n"

    elif "real" in type_validation:
        dsl += "enum Value {"
        exs_in = [float(ex.input[0]) for ex in filter(lambda x: x.output == True, examples)]
        min_in, max_in = min(exs_in), max(exs_in)
        dsl += f'"{str(min_in)}", "{str(max_in)}"'
        dsl += "}\n"

    dsl += dsl_base

    return dsl



