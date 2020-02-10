#!/usr/bin/env python
import argparse
import sys

import tyrell.spec as S
from build_dsl import build_dsl
from input_parser import parse_file
from type_checker import check_type
from tyrell.enumerator import SmtEnumerator
from tyrell.decider import ExampleConstraintDecider, ExampleConstraintPruningDecider
from tyrell.synthesizer import Synthesizer
from tyrell.logger import get_logger
from validation_interpreter import ValidationInterpreter
from validation_printer import ValidationPrinter

logger = get_logger('tyrell')


def my_equal_output(program, input, desired_output):
    interpreter = ValidationInterpreter()
    try:
        output = interpreter.eval(program, input)
        return output == desired_output
    except Exception as e:
        print("exception", e, file=sys.stderr)
        return False == desired_output

def main():
    parser = argparse.ArgumentParser(description='Validations Synthesizer')
    parser.add_argument('-f', '--file', dest="file", type=str, help='file with I/O examples')
    parser.add_argument('-d', '--debug', action='store_true', help='debug mode')

    args = parser.parse_args()
    if args.debug:
        logger.setLevel("DEBUG")
    else:
        logger.setLevel("INFO")

    if not args.file:
        io_file = "instances/PostalCodesPortugal.txt"
    else:
        io_file = args.file

    logger.info("Parsing examples from file " + io_file)
    examples = parse_file(io_file)

    type_validation, examples = check_type(examples)

    logger.info("assuming types: " + str(type_validation))
    logger.debug("remaining examples:" + str(examples))
    dsl = build_dsl(type_validation, examples)
    logger.debug("using DSL:\n" + dsl)
    dsl = S.parse(dsl)

    printer = ValidationPrinter()
    maxdep = 6
    for dep in range(3, maxdep+1):
        logger.info(f'Synthesizing programs of depth {dep}')
        enumerator = SmtEnumerator(dsl, depth=dep, loc=4)
        synthesizer = Synthesizer(
            enumerator=enumerator,
            decider=ExampleConstraintDecider(
                spec=dsl,
                interpreter=ValidationInterpreter(),
                examples=examples,
                equal_output=my_equal_output
            ),
            printer=printer
        )
        program = synthesizer.synthesize()

        if program is not None:
            logger.info('Solution found: ' + type_validation[0] + "(IN) /\\ " + printer.eval(program, ["IN"]))
            logger.info(f'depth: {dep}')
            return



    logger.info('Solution not found!')


if __name__ == '__main__':
    main()
