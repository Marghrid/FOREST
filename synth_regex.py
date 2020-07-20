#!/usr/bin/env python3
import argparse
import random
from signal import signal, SIGINT, SIGTERM

from termcolor import colored

from forest.dsl.dsl_builder import DSLBuilder
from forest.logger import get_logger
from forest.parse_examples import parse_file, parse_resnax
from forest.synthesizer import MultiTreeSynthesizer, KTreeSynthesizer, LinesSynthesizer, \
    SketchSynthesizer
from forest.visitor import RegexInterpreter

logger = get_logger('forest')

synthesizer = None


def sig_handler(received_signal, frame):
    print('\nSIGINT or SIGTERM detected. Exiting gracefully.')
    if synthesizer is not None:
        print('Printing the last valid program found.')
        synthesizer.die = True


def main():
    signal(SIGINT, sig_handler)
    signal(SIGTERM, sig_handler)
    examples_file, encoding, self_interact, resnax, no_pruning, max_valid, max_invalid, \
    sketching_mode = read_cmd_args()

    if resnax:
        valid, invalid, ground_truth = parse_resnax(examples_file)
    else:
        valid, invalid, condition_invalid, ground_truth = parse_file(examples_file)

    random.seed("regex")
    if 0 < max_valid < len(valid):
        valid = random.sample(valid, max_valid)
    if 0 < max_invalid < len(invalid):
        invalid = random.sample(invalid, max_invalid)

    show(valid, invalid, condition_invalid, ground_truth)
    if sketching_mode != 'none':
        sketch_synthesize(valid, invalid, condition_invalid, sketching_mode, ground_truth, self_interact,
                          no_pruning)
    elif encoding == 'multitree':
        multitree_synthesize(valid, invalid, condition_invalid, ground_truth, self_interact, no_pruning)
    elif encoding == "dynamic":
        dynamic_synthesize(valid, invalid, condition_invalid, ground_truth, self_interact, no_pruning)
    elif encoding == 'ktree':
        ktree_synthesize(valid, invalid, condition_invalid, ground_truth, self_interact, no_pruning)
    elif encoding == 'lines':
        lines_synthesize(valid, invalid, condition_invalid, ground_truth, self_interact, no_pruning)
    else:
        raise ValueError


def show(valid, invalid, condition_invalid, ground_truth: str):
    print(len(valid), "valid examples:")
    max_len = max(map(lambda x: sum(map(len, x)) + 2 * len(x), valid))
    max_len = max(max_len, 6)
    line_len = 0
    for ex in valid:
        s = ', '.join(ex).center(max_len)
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

    print(len(condition_invalid), "condition invalid examples:")
    max_len = max(map(lambda x: len(x[0]), condition_invalid))
    max_len = max(max_len, 6)
    line_len = 0
    for ex in condition_invalid:
        s = f'{ex[0]}'.center(max_len)
        line_len += len(s)
        print(colored(s, "magenta"), end='  ')
        if line_len > 70:
            line_len = 0
            print()
    print()
    print("Ground truth:")
    print(colored(ground_truth, "green"))


def multitree_synthesize(valid, invalid, condition_invalid, ground_truth=None, self_interact=False,
                         no_pruning=False):
    global synthesizer
    dsl, valid, invalid, captures, type_validation = prepare_things(valid, invalid)
    if "string" not in type_validation[0] and "regex" not in type_validation[0]:
        raise Exception("MultiTree Synthesizer is only for strings.")
    synthesizer = MultiTreeSynthesizer(valid, invalid, captures, condition_invalid, dsl,
                                       ground_truth, pruning=not no_pruning,
                                       auto_interaction=self_interact)
    return synthesize(type_validation)


def sketch_synthesize(valid, invalid, sketching_mode, ground_truth=None,
                      self_interact=False,
                      no_pruning=False, ):
    global synthesizer
    dsl, valid, invalid, captures, type_validation = prepare_things(valid, invalid, sketch=True)
    if "string" not in type_validation[0] and "regex" not in type_validation[0]:
        raise Exception("MultiTree Synthesizer is only for strings.")
    synthesizer = SketchSynthesizer(valid, invalid, dsl, ground_truth, sketching_mode,
                                    auto_interaction=self_interact)
    return synthesize(type_validation)


def dynamic_synthesize(valid, invalid, condition_invalid, ground_truth=None, self_interact=False,
                       no_pruning=False):
    global synthesizer
    dsl, valid, invalid, captures, type_validation = prepare_things(valid, invalid)
    synthesizer = MultiTreeSynthesizer(valid, invalid, dsl, ground_truth,
                                       pruning=not no_pruning,
                                       auto_interaction=self_interact, force_dynamic=True)
    return synthesize(type_validation)


def ktree_synthesize(valid, invalid, ground_truth=None, self_interact=False,
                     no_pruning=False):
    global synthesizer
    dsl, valid, invalid, captures, type_validation = prepare_things(valid, invalid)
    synthesizer = KTreeSynthesizer(valid, invalid, dsl, ground_truth,
                                   pruning=not no_pruning, auto_interaction=self_interact)
    return synthesize(type_validation)


def lines_synthesize(valid, invalid, ground_truth=None, self_interact=False,
                     no_pruning=False):
    global synthesizer
    dsl, valid, invalid, captures, type_validation = prepare_things(valid, invalid)
    synthesizer = LinesSynthesizer(valid, invalid, dsl, ground_truth,
                                   pruning=not no_pruning, auto_interaction=self_interact)
    return synthesize(type_validation)


def prepare_things(valid, invalid, sketch=False):
    type_validation = ["regex"]
    if len(valid) == 0:
        raise ValueError("No valid examples!")
    if isinstance(valid[0], str):
        valid = list(map(lambda v: [v], valid))
    if isinstance(invalid[0], str):
        invalid = list(map(lambda v: [v], invalid))
    # logger.info("Assuming types: " + str(type_validation))
    captures = list(map(lambda x: x[1:], valid))
    valid = list(map(lambda x: [x[0]], valid))
    builder = DSLBuilder(type_validation, valid, invalid, sketch)
    dsl = builder.build()[0]
    # TODO: build() returns a list of DSLs for each different type of element. Now I'm
    #  just using the first element

    return dsl, valid, invalid, captures, type_validation


def synthesize(type_validation):
    global synthesizer
    assert synthesizer is not None
    printer = RegexInterpreter()
    program = synthesizer.synthesize()
    if program is not None:
        p = program[0]
        c = program[1]
        print(colored(f'Solution: {printer.eval(p, captures=c)}', "green"))
    else:
        print('Solution not found!')
    return program


# noinspection PyTypeChecker
def read_cmd_args():
    encodings = ('multitree', 'dynamic', 'ktree', 'lines')
    sketching = ('none', 'smt', 'brute-force', 'hybrid')
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
    parser.add_argument('-k', '--sketch', metavar='|'.join(sketching), type=str,
                        default='none', help='Enable sketching.')
    args = parser.parse_args()
    if args.debug:
        logger.setLevel("DEBUG")
    else:
        logger.setLevel("INFO")
    if args.encoding not in encodings:
        raise ValueError('Unknown encoding ' + args.encoding)

    return args.file, args.encoding, args.self_interact, args.resnax, args.no_pruning, \
           args.max_valid, args.max_invalid, args.sketch


if __name__ == '__main__':
    main()
