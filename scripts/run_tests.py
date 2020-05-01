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


def main():
    signal(SIGINT, handler)
    methods = ('multitree', 'funny', 'ktree', 'nopruning', 'compare-times')

    parser = argparse.ArgumentParser(description='Validations Synthesizer tester')
    parser.add_argument('directories', type=str, metavar="dir", nargs='+', help='Directories with instances')
    parser.add_argument('-p', '--processes', metavar="P", type=int, help='Number of processes. Default: 1.', default=1)
    parser.add_argument('-r', '--run-each', metavar="R", type=int,
                        help='Number of times to run each instance. Default: 1.', default=1)
    parser.add_argument('-t', '--timeout', metavar="T", type=int, help='Timeout in seconds. Default: 120.', default=120)
    parser.add_argument('-o', '--out', action='store_true', help='Show output. Default: False.', default=False)
    parser.add_argument('-m', '--method', metavar='|'.join(methods), type=str, default='multitree',
                        help='Method of synthesis. Default: multitree.')
    parser.add_argument('--resnax', action='store_true', help='read resnax i/o examples format.')

    args = parser.parse_args()

    if args.method not in methods:
        raise ValueError('Unknown method ' + args.method)

    global tester

    tester = Tester(args.directories, args.method, args.processes, args.run_each, args.timeout, args.out, args.resnax)
    tester.test()
    if args.method == 'compare-times':
        tester.print_time_comparison()
    else:
        tester.print_results()


if __name__ == '__main__':
    main()
