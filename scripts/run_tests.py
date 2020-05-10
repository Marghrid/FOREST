#!/usr/bin/env python3

import argparse
from signal import signal, SIGINT

from tester import Tester

tester = None


def handler(signal_received, frame):
    # Handle any cleanup here
    print('\nSIGINT or CTRL-C detected. Exiting gracefully.')
    if tester is not None:
        tester.terminate_all()
    exit()


# noinspection PyTypeChecker
def main():
    signal(SIGINT, handler)
    methods = ('multitree', 'funny', 'ktree', 'nopruning', 'compare-times')

    parser = argparse.ArgumentParser(description='Validations Synthesizer tester',
                                     formatter_class=argparse.ArgumentDefaultsHelpFormatter)
    parser.add_argument('directories', type=str, metavar="dir", nargs='+',
                        help='Directories with instances')
    parser.add_argument('-p', '--processes', metavar="P", type=int,
                        help='Number of processes.', default=1)
    parser.add_argument('-r', '--run-each', metavar="R", type=int,
                        help='Number of times to run each instance.', default=1)
    parser.add_argument('-t', '--timeout', metavar="T", type=int,
                        help='Timeout in seconds.', default=120)
    parser.add_argument('-o', '--out', action='store_true',
                        help='Show output.', default=False)

    synth_group = parser.add_argument_group(title="Synthesizer options")
    synth_group.add_argument('-m', '--method', metavar='|'.join(methods), type=str,
                        default='multitree', help='Method of synthesis.')
    synth_group.add_argument('--resnax', action='store_true',
                        help='read resnax i/o examples format.')
    synth_group.add_argument('-v', '--max-valid', type=int, default=-1,
                        help='Limit the number of valid examples. -1: unlimited.')
    synth_group.add_argument('-i', '--max-invalid', type=int, default=-1,
                        help='Limit the number of invalid examples. -1: unlimited.')

    args = parser.parse_args()

    if args.method not in methods:
        raise ValueError('Unknown method ' + args.method)

    global tester

    tester = Tester(args.directories, args.method, args.processes, args.run_each,
                    args.timeout, args.out, args.resnax, args.max_valid, args.max_invalid)
    tester.test()
    if args.method == 'compare-times':
        tester.print_time_comparison()
    else:
        tester.print_results()


if __name__ == '__main__':
    main()
