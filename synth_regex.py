#!/usr/bin/python
import argparse
import random
from signal import signal, SIGINT, SIGTERM

from termcolor import colored

from tyrell.dslBuilder import DSLBuilder
from tyrell.interpreter import ValidationPrinter
from tyrell.logger import get_logger
from tyrell.parse_examples import parse_file, parse_resnax
from tyrell.synthesizer import MultiTreeSynthesizer, KTreeSynthesizer, LinesSynthesizer

logger = get_logger('tyrell')

synthesizer = None


def sig_handler(received_signal, frame):
    print('\nSIGINT or SIGTERM detected. Exiting gracefully.')
    if synthesizer is not None:
        print('Printing the last valid program found.')
        synthesizer.die = True


def main():
    signal(SIGINT, sig_handler)
    signal(SIGTERM, sig_handler)
    examples_file, encoding, self_interact, resnax, no_pruning, max_valid, max_invalid = read_cmd_args()

    if resnax:
        valid, invalid, ground_truth = parse_resnax(examples_file)
    else:
        valid, invalid, ground_truth = parse_file(examples_file)

    random.seed("regex")
    if max_valid > 0 and max_valid < len(valid):
        valid = random.sample(valid, max_valid)
    if max_invalid > 0 and max_invalid < len(invalid):
        invalid = random.sample(invalid, max_invalid)

    show(valid, invalid, ground_truth)
    if encoding == 'multitree':
        multitree_synthesize(valid, invalid, ground_truth, self_interact, no_pruning)
    elif encoding == "funny":
        funny_synthesize(valid, invalid, ground_truth, self_interact, no_pruning)
    elif encoding == 'ktree':
        ktree_synthesize(valid, invalid, ground_truth, self_interact, no_pruning)
    elif encoding == 'lines':
        lines_synthesize(valid, invalid, ground_truth, self_interact, no_pruning)
    else:
        raise ValueError


def show(valid, invalid, ground_truth: str):
    print(len(valid), "valid examples:")
    max_len = max(map(lambda x: len(x[0]), valid))
    max_len = max(max_len, 6)
    line_len = 0
    for ex in valid:
        s = f'{ex[0]}'.center(max_len)
        line_len += len(s)
        print(colored(s, "blue"), end='  ')
        if line_len > 70:
            line_len = 0
            print()
    print()

    print(len(invalid), "invalid examples:")
    max_len = max(map(lambda x: len(x[0]), invalid))
    max_len = max(max_len, 6)
    line_len = 0
    for ex in invalid:
        s = f'{ex[0]}'.center(max_len)
        line_len += len(s)
        print(colored(s, "red"), end='  ')
        if line_len > 70:
            line_len = 0
            print()
    print()
    print("Ground truth:")
    print(colored(ground_truth, "green"))


def multitree_synthesize(valid, invalid, ground_truth, self_interact=False, no_pruning=False):
    global synthesizer
    dsl, valid, invalid, type_validation = prepare_things(valid, invalid)
    if "string" not in type_validation[0]:
        raise Exception("MultiTree Synthesizer is only for strings.")
    synthesizer = MultiTreeSynthesizer(valid, invalid, dsl, ground_truth,
                                       pruning=not no_pruning, auto_interaction=self_interact)
    return synthesize(synthesizer, type_validation)


def funny_synthesize(valid, invalid, ground_truth, self_interact=False, no_pruning=False):
    global synthesizer
    dsl, valid, invalid, type_validation = prepare_things(valid, invalid)
    if "string" not in type_validation[0]:
        raise Exception("GreedySynthesizer is only for strings.")
    synthesizer = MultiTreeSynthesizer(valid, invalid, dsl, ground_truth,
                                       pruning=not no_pruning, auto_interaction=self_interact, force_funny=True)
    return synthesize(synthesizer, type_validation)


def ktree_synthesize(valid, invalid, ground_truth, self_interact=False, no_pruning=False):
    global synthesizer
    dsl, valid, invalid, type_validation = prepare_things(valid, invalid)
    synthesizer = KTreeSynthesizer(valid, invalid, dsl, ground_truth,
                                   pruning=not no_pruning, auto_interaction=self_interact)
    return synthesize(synthesizer, type_validation)


def lines_synthesize(valid, invalid, ground_truth, self_interact=False, no_pruning=False):
    global synthesizer
    dsl, valid, invalid, type_validation = prepare_things(valid, invalid)
    synthesizer = LinesSynthesizer(valid, invalid, dsl, ground_truth,
                                   pruning=not no_pruning, auto_interaction=self_interact)
    return synthesize(synthesizer, type_validation)

def prepare_things(valid, invalid):
    type_validation = ["is_string"]
    # logger.info("Assuming types: " + str(type_validation))
    builder = DSLBuilder(type_validation, valid, invalid)
    dsl = builder.build()[0]
    # TODO: build() returns a list of DSLs for each different type of element. Now I'm
    #  just using the first element

    return dsl, valid, invalid, type_validation


def synthesize(synthesizer, type_validation):
    printer = ValidationPrinter()
    program = synthesizer.synthesize()
    if program is not None:
        logger.info(
            colored(f'Solution: {printer.eval(program, ["IN"])}', "green"))
    else:
        logger.info('Solution not found!')


# noinspection PyTypeChecker
def read_cmd_args():
    encodings = ('multitree', 'funny', 'ktree', 'lines')
    parser = argparse.ArgumentParser(description='Validations Synthesizer',
                                     formatter_class=argparse.ArgumentDefaultsHelpFormatter)
    parser.add_argument('file', type=str, help='File with I/O examples.')
    parser.add_argument('-d', '--debug', action='store_true', help='Debug mode.')
    parser.add_argument('-e', '--encoding', metavar='|'.join(encodings), type=str,
                        default='multitree', help='SMT encoding.')
    parser.add_argument('-s', '--self-interact', action="store_true",
                        help="Self interaction mode.")
    parser.add_argument('--no-pruning', '--nopruning', action='store_true',
                        help='Disable pruning.')
    parser.add_argument('--resnax', action='store_true',
                        help='Read resnax i/o examples format.')
    parser.add_argument('-v', '--max-valid', type=int, default=-1,
                        help='Limit the number of valid examples. -1: unlimited.')
    parser.add_argument('-i', '--max-invalid', type=int, default=-1,
                        help='Limit the number of invalid examples. -1: unlimited.')
    args = parser.parse_args()
    if args.debug:
        logger.setLevel("DEBUG")
    else:
        logger.setLevel("INFO")
    if args.encoding not in encodings:
        raise ValueError('Unknown encoding ' + args.encoding)

    return args.file, args.encoding, args.self_interact, args.resnax, args.no_pruning, args.max_valid, args.max_invalid


if __name__ == '__main__':
    main()
