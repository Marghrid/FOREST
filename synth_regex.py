#!/usr/bin/python
import argparse

from termcolor import colored

from tyrell.dslBuilder import DSLBuilder
from tyrell.parse_examples import parse_file
from tyrell.interpreter import ValidationPrinter
from tyrell.logger import get_logger
from tyrell.synthesizer import MultiTreeSynthesizer, KTreeSynthesizer

logger = get_logger('tyrell')


def main():
    examples_file, synth_method = read_cmd_args()
    show(examples_file)
    if synth_method == 'multitree':
        multitree_synthesize(examples_file)
    elif synth_method == 'ktree':
        ktree_synthesize(examples_file)
    elif synth_method == 'nopruning':
        multitree_nopruning_synthesize(examples_file)
    else:
        raise ValueError


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


def multitree_synthesize(examples_file):
    dsl, valid, invalid, type_validation = prepare_things(examples_file)
    if "string" not in type_validation[0]:
        raise Exception("GreedySynthesizer is only for strings.")
    synthesizer = MultiTreeSynthesizer(valid, invalid, dsl)
    synthesize(synthesizer, type_validation)


def ktree_synthesize(examples_file):
    dsl, valid, invalid, type_validation = prepare_things(examples_file)
    synthesizer = KTreeSynthesizer(valid, invalid, dsl)
    synthesize(synthesizer, type_validation)


def multitree_nopruning_synthesize(examples_file):
    dsl, valid, invalid, type_validation = prepare_things(examples_file)
    if "string" not in type_validation[0]:
        raise Exception("GreedySynthesizer is only for strings.")
    synthesizer = MultiTreeSynthesizer(valid, invalid, dsl, pruning=False)
    synthesize(synthesizer, type_validation)


def prepare_things(examples_file):
    logger.info("Parsing examples from file " + examples_file)
    valid, invalid = parse_file(examples_file)
    type_validation = ["is_string"]
    # logger.info("Assuming types: " + str(type_validation))
    builder = DSLBuilder(type_validation, valid, invalid)
    dsl = builder.build()[0]
    # TODO: build() returns a list of DSLs for each different type of element. Now I'm just using the first element

    return dsl, valid, invalid, type_validation


def synthesize(synthesizer, type_validation):
    printer = ValidationPrinter()
    program = synthesizer.synthesize()
    if program is not None:
        logger.info(
            colored(f'Solution: {printer.eval(program, ["IN"])}', "green"))
    else:
        logger.info('Solution not found!')


def read_cmd_args():
    methods = ('multitree', 'ktree', 'nopruning')
    parser = argparse.ArgumentParser(description='Validations Synthesizer')
    parser.add_argument('file', type=str, help='file with I/O examples')
    parser.add_argument('-d', '--debug', action='store_true', help='debug mode')
    parser.add_argument('-m', '--method', metavar='|'.join(methods), type=str, default='multitree',
                        help='Method of synthesis. Default: multitree.')
    args = parser.parse_args()
    if args.debug:
        logger.setLevel("DEBUG")
    else:
        logger.setLevel("INFO")
    if args.method not in methods:
        raise ValueError('Unknown method ' + args.method)

    return args.file, args.method


if __name__ == '__main__':
    main()
