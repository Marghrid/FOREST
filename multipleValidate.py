#!/usr/bin/python
import argparse
import time

from termcolor import colored
from build_dsl import DSLBuilder
from examples_parser import parse_file
from type_checker import check_type
from tyrell.decider import ValidationDecider, Example
from tyrell.enumerator import SmtEnumerator, FunnyEnumerator
from tyrell.interpreter import ValidationInterpreter, ValidationPrinter
from tyrell.logger import get_logger
from tyrell.synthesizer import MultipleSynthesizer

logger = get_logger('tyrell')

def main():
    examples_file = read_cmd_args()
    funnySynthesize(examples_file)


def show(examples_file):
    valid_examples, invalid_examples = parse_file(examples_file)
    print("Valid examples:")
    for ex in valid_examples:
        print(colored('  ' + str(ex), "blue"))

    print("Invalid examples:")
    for ex in invalid_examples:
        print(colored('  ' + str(ex), "red"))

def synthesize(examples_file):
    logger.info("Parsing examples from file " + examples_file)
    valid, invalid = parse_file(examples_file)
    type_validation, valid, invalid = check_type(valid, invalid)
    # logger.info("Assuming types: " + str(type_validation))
    logger.debug("Remaining invalid examples:" + str(invalid))
    builder = DSLBuilder(type_validation, valid, invalid)
    dsl = builder.build()[0]
    # TODO: build() returns a list of DSLs for each different type of element. Now I'm just using the first element
    examples = [Example(x, True) for x in valid] + [Example(x, False) for x in invalid]
    printer = ValidationPrinter()
    decider = ValidationDecider(
        spec=dsl,
        interpreter=ValidationInterpreter(),
        examples=examples
    )
    maxdep = 6
    program = None
    start_time = time.time()
    for dep in range(3, maxdep + 1):
        logger.debug(f'Synthesizing programs of depth {dep}')
        enumerator = SmtEnumerator(dsl, depth=dep, loc=4)
        synthesizer = MultipleSynthesizer(
            enumerator=enumerator,
            decider=decider,
            printer=printer
        )
        program = synthesizer.synthesize()

        if program is not None:
            logger.info(colored('Solution: ' + type_validation[0] + "(IN) /\\ " + printer.eval(program, ["IN"]), "green"))
            logger.info(f'depth: {dep}, elapsed: {round(time.time() - start_time)} seconds.')
            break
    if program is None:
        logger.info('Solution not found!')

def funnySynthesize(examples_file):
    logger.info("Parsing examples from file " + examples_file)
    valid, invalid = parse_file(examples_file)
    type_validation, valid, invalid = check_type(valid, invalid)
    # logger.info("Assuming types: " + str(type_validation))
    logger.debug("Remaining invalid examples:" + str(invalid))
    builder = DSLBuilder(type_validation, valid, invalid)
    dsl = builder.build()[0]
    # TODO: build() returns a list of DSLs for each different type of element. Now I'm just using the first element
    examples = [Example(x, True) for x in valid] + [Example(x, False) for x in invalid]
    printer = ValidationPrinter()
    decider = ValidationDecider(
        spec=dsl,
        interpreter=ValidationInterpreter(),
        examples=examples
    )
    maxdep = 6
    program = None
    start_time = time.time()
    for dep in range(2, maxdep + 1):
        for leng in range(1, 3*dep):
            logger.debug(f'Synthesizing programs of depth {dep} and length {leng}')
            enumerator = FunnyEnumerator(dsl, depth=dep, length=leng)
            synthesizer = MultipleSynthesizer(
                enumerator=enumerator,
                decider=decider,
                printer=printer
            )
            program = synthesizer.synthesize()

            if program is not None:
                logger.info(colored('Solution: ' + type_validation[0] + "(IN) /\\ " + printer.eval(program, ["IN"]), "green"))
                logger.info(f'depth: {dep}, length {leng}, elapsed: {round(time.time() - start_time)} seconds.')
                break
        if program is not None:
            break
    if program is None:
        logger.info('Solution not found!')


def singleSynthesize(examples_file):
    logger.info("Parsing examples from file " + examples_file)
    valid, invalid = parse_file(examples_file)
    type_validation, valid, invalid = check_type(valid, invalid)
    logger.info("Assuming types: " + str(type_validation))
    logger.debug("Remaining invalid examples:" + str(invalid))
    builder = DSLBuilder(type_validation, valid, invalid)
    dsl = builder.build()[0]

    # TODO: build() returns a list of DSLs for each different type of element. Now I'm just using the first element
    examples = [Example(x, True) for x in valid] + [Example(x, False) for x in invalid]
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

def read_cmd_args():
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
