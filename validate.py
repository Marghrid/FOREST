#!/usr/bin/python
import argparse

from build_dsl import DSLBuilder
from examples_parser import parse_file
from type_checker import check_type
from tyrell.decider import ValidationDecider, Example
from tyrell.enumerator import SmtEnumerator
from tyrell.interpreter.validation_interpreter import ValidationInterpreter
from tyrell.interpreter.validation_printer import ValidationPrinter
from tyrell.logger import get_logger
from tyrell.synthesizer import Synthesizer




def main():
    logger = get_logger('tyrell')
    examples_file = read_cmd_args(logger)

    logger.info("Parsing examples from file " + examples_file)
    valid_examples, invalid_examples = parse_file(examples_file)

    type_validation, valid_examples, invalid_examples = check_type(valid_examples, invalid_examples)
    logger.info("Assuming types: " + str(type_validation))
    logger.debug("Remaining invalid examples:" + str(invalid_examples))

    # TODO create DSL as spec object instead of string
    builder = DSLBuilder(type_validation, valid_examples, invalid_examples)
    dsl = builder.build()[0]
    # TODO: build() returns a list of DSLs for each different type of element. Now I'm just using the first element
    # logger.debug("Using DSL:\n" + str(dsl))

    examples = [Example(x, True) for x in valid_examples] + [Example(x, False) for x in invalid_examples]

    printer = ValidationPrinter()
    decider = ValidationDecider(
        spec=dsl,
        interpreter=ValidationInterpreter(),
        examples=examples
    )
    maxdep = 6
    for dep in range(3, maxdep + 1):
        logger.info(f'Synthesizing programs of depth {dep}')
        enumerator = SmtEnumerator(dsl, depth=dep, loc=4)
        synthesizer = Synthesizer(
            enumerator=enumerator,
            decider=decider,
            printer=printer
        )
        program = synthesizer.synthesize()

        if program is not None:
            logger.info('Solution found: ' + type_validation[0] + "(IN) /\\ " + printer.eval(program, ["IN"]))
            logger.info(f'depth: {dep}')
            return

    logger.info('Solution not found!')


def read_cmd_args(logger):
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
    return io_file


if __name__ == '__main__':
    main()
