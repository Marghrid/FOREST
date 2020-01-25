#!/usr/bin/env python
import re

import tyrell.spec as S
from input_parser import parse_file
from type_checker import check_type
from tyrell.enumerator import SmtEnumerator
from tyrell.decider import Example, ExampleConstraintDecider
from tyrell.synthesizer import Synthesizer
from tyrell.logger import get_logger
from validation_interpreter import ValidationInterpreter
from validation_interpreter import ValidationPrinter

logger = get_logger('tyrell')


def my_equal_output(program, input, desired_output):
    interpreter = ValidationInterpreter()
    try:
        output = interpreter.eval(program, input)
        return output == desired_output
    except:
        return False == desired_output


def pick_dsl(type_validation):
    type_validation = type_validation[0]
    return "DSLs/" + re.sub('^is_', '', type_validation) + "DSL.tyrell"


def main():
    logger.info('Parsing Spec...')
    logger.info('Parsing succeeded')
    logger.info('Building synthesizer...')

    examples = parse_file("instances/age1.txt")
    print(examples)

    type_validation, examples = check_type(examples)

    dsl_file = pick_dsl(type_validation)
    spec = S.parse_file(dsl_file)

    printer = ValidationPrinter()
    dep = 4
    enumerator = SmtEnumerator(spec, depth=dep, loc=4)
    synthesizer = Synthesizer(
        enumerator=enumerator,
        decider=ExampleConstraintDecider(
            spec=spec,
            interpreter=ValidationInterpreter(),
            examples=examples,
            equal_output=my_equal_output
        ),
        printer=printer
    )
    logger.info(f'Synthesizing programs of depth {dep}')

    prog = synthesizer.synthesize()
    if prog is not None:
        logger.info('Solution found: ' + type_validation[0] + "(IN) /\\ " + printer.eval(prog, ["IN"]))
        logger.info(f'depth: {dep}')
        return
    logger.info('Solution not found!')


if __name__ == '__main__':
    logger.setLevel('INFO')
    main()
