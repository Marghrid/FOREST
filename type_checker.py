import itertools
from typing import List
from tyrell.decider import Example


def is_integer(arg: str):
    try:
        int(arg)
        return True
    except:
        return False


def is_real(arg: str):
    try:
        float(arg)
        return True
    except:
        return False

def is_string(arg:str):
    return True


possible_types_validations = [is_integer, is_real, is_string]


def check_type(valid: List, invalid: List):
    num_fields = len(valid[0])
    types = []

    # discard outputs
    if len(valid) > 0:
        # separate by field
        transposed_valid = list(map(list, zip(*valid)))
    else:
        transposed_valid = [[]]

    if len(invalid) > 0:
        transposed_invalid = list(map(list, zip(*invalid)))
    else:
        transposed_invalid = [[]]

    # separate by field

    for field_idx in range(num_fields):
        for validation in possible_types_validations:
            if all(map(validation, transposed_valid[field_idx])): # this validation is verified for all valid examples
                if any(list(map(validation, transposed_invalid[field_idx]))):
                    eliminated = list(map(validation, transposed_invalid[field_idx]))
                    
                    assert len(eliminated) == len(invalid)
                    # remove from invalid examples those that are cleared up by this validation:
                    invalid = list(itertools.compress(invalid, eliminated))
                    types.append(validation.__name__)
                else:
                    types.append(validation.__name__)
                break

    return types, valid, invalid

