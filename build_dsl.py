import re


def build_dsl(type_validation):
    type_validation = type_validation[0]
    return "DSLs/" + re.sub('^is_', '', type_validation) + "DSL.tyrell"