#!/usr/bin/python
import argparse
import itertools
import time

from termcolor import colored

from tyrell.decider import ValidationDecider, Example
from tyrell.dslBuilder import DSLBuilder
from tyrell.enumerator import KTreeEnumerator, FunnyEnumerator
from tyrell.parse_examples import parse_file
from tyrell.interpreter import ValidationInterpreter, ValidationPrinter
from tyrell.logger import get_logger
from tyrell.synthesizer import MultipleSynthesizer, SingleSynthesizer, GreedySynthesizer
from tyrell.type_checker import check_type

logger = get_logger('tyrell')


def main():
    examples_file = read_cmd_args()
    greedy_synthesize(examples_file)
    # greedy_synthesize_valid(examples_file)
    # synthesize(examples_file)
    # single_synthesize(examples_file)


def show(examples_file):
    valid_examples, invalid_examples = parse_file(examples_file)
    print("Valid examples:")
    max_len = max(map(lambda x: len(x[0]), valid_examples))
    max_len = max(max_len, 6)
    for i, ex in enumerate(valid_examples):
        print(colored(f'{ex[0]}'.center(max_len), "blue"), end='  ')
        if (i + 1) % 5 == 0:
            print()
    print()

    print("Invalid examples:")
    max_len = max(map(lambda x: len(x[0]), invalid_examples))
    max_len = max(max_len, 6)
    for i, ex in enumerate(invalid_examples):
        print(colored(f'{ex[0]}'.center(max_len), "red"), end='  ')
        if (i + 1) % 5 == 0:
            print()
    print()


def prepare_things(examples_file):
    logger.info("Parsing examples from file " + examples_file)
    valid, invalid = parse_file(examples_file)
    type_validation, valid, invalid = check_type(valid, invalid)
    if "AlphaRegex" in examples_file:
        type_validation = ["is_string"]
    # logger.info("Assuming types: " + str(type_validation))
    logger.debug("Remaining invalid examples:" + str(invalid))
    builder = DSLBuilder(type_validation, valid, invalid)
    dsl = builder.build()[0]
    # TODO: build() returns a list of DSLs for each different type of element. Now I'm just using the first element

    return dsl, valid, invalid, type_validation


def greedy_synthesize(examples_file):
    dsl, valid, invalid, type_validation = prepare_things(examples_file)
    if "string" not in type_validation[0]:
        raise Exception("Synth-19 is only for strings.")
    printer = ValidationPrinter()
    synthesizer = GreedySynthesizer(valid, invalid, dsl)
    program = synthesizer.synthesize()
    if program is not None:
        logger.info(
            colored(f'Solution: {type_validation[0]}(IN) /\\ {printer.eval(program, ["IN"])}', "green"))
    else:
        logger.info('Solution not found!')

def greedy_synthesize_valid(examples_file):
    dsl, valid, _, type_validation = prepare_things(examples_file)
    if "string" not in type_validation[0]:
        raise Exception("Synth-19 is only for strings.")
    synthesizer = GreedySynthesizer(valid, [], dsl)
    printer = ValidationPrinter()
    program = synthesizer.synthesize()
    if program is not None:
        logger.info(
            colored(f'Solution: {type_validation[0]}(IN) /\\ {printer.eval(program, ["IN"])}', "green"))
    else:
        logger.info('Solution not found!')

def synthesize(examples_file):
    dsl, valid, invalid, type_validation = prepare_things(examples_file)
    synthesizer = MultipleSynthesizer(valid, invalid, dsl)
    printer = ValidationPrinter()
    program = synthesizer.synthesize()
    if program is not None:
        logger.info(
            colored(f'Solution: {type_validation[0]}(IN) /\\ {printer.eval(program, ["IN"])}', "green"))
    else:
        logger.info('Solution not found!')


def single_synthesize(examples_file):
    dsl, valid, invalid, type_validation = prepare_things(examples_file)
    synthesizer = SingleSynthesizer(valid, invalid, dsl)
    printer = ValidationPrinter()
    program = synthesizer.synthesize()
    if program is not None:
        logger.info(
            colored(f'Solution: {type_validation[0]}(IN) /\\ {printer.eval(program, ["IN"])}', "green"))
    else:
        logger.info('Solution not found!')


def read_cmd_args():
    parser = argparse.ArgumentParser(description='Validations Synthesizer')
    parser.add_argument('file', type=str, help='file with I/O examples')
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
