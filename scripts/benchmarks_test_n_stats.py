import argparse
import glob
# noinspection PyTypeChecker
from dataclasses import dataclass
from operator import add
from statistics import median, mean

from termcolor import colored

from forest.parse_examples import parse_resnax, parse_file

exclude_instances = ["datetime2"]  # , "color", "date", "date7", "id1", "date3"]


@dataclass
class InstanceStats:
    name: str
    path: str
    num_valid: int
    num_invalid: int
    num_cond_invalid: int


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

    if len(condition_invalid) > 0:
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
    else:
        print("No condition invalid examples.")
    print("Ground truth:")
    print(colored(ground_truth, "green"))


def main():
    parser = argparse.ArgumentParser(description='Benchmarks tester',
                                     formatter_class=argparse.ArgumentDefaultsHelpFormatter)
    parser.add_argument('directories', type=str, metavar="dir", nargs='+',
                        help='Directories with instances')
    parser.add_argument('--resnax', action='store_true',
                        help='read resnax i/o examples format.')
    args = parser.parse_args()

    instances = []

    for d in args.directories:
        instance_paths = glob.glob(d + "/*.txt")
        instances.extend(instance_paths)

    instance_stats = []
    for instance in instances:
        if args.resnax:
            valid, invalid, ground_truth = parse_resnax(instance)
            cond_invalid = []
        else:
            valid, invalid, cond_invalid, ground_truth = parse_file(instance)

        show(valid, invalid, cond_invalid, ground_truth)

        inst_name = instance.split("/")[-1]
        inst_name = inst_name.replace(".txt", "", 1)

        new_stat = InstanceStats(inst_name, instance, len(valid), len(invalid), len(cond_invalid))
        instance_stats.append(new_stat)

    instance_stats = list(filter(lambda s: s.name not in exclude_instances, instance_stats))

    all_num_valid = list(map(lambda s: s.num_valid, instance_stats))
    all_num_invalid = list(map(lambda s: s.num_invalid, instance_stats))
    all_num_cond_invalid = list(map(lambda s: s.num_cond_invalid, instance_stats))
    all_num_exs = list(map(add, all_num_valid, map(add, all_num_invalid, all_num_cond_invalid)))
    print(list(enumerate(all_num_exs)))
    print(list(enumerate(map(lambda i: i.name, instance_stats))))
    all_num_cond_invalid = list(filter(lambda x: x > 0, all_num_cond_invalid))

    print("Total instances:", len(instance_stats))
    for i in list(filter(lambda s: s.num_cond_invalid > 0, instance_stats)):
        print(i.name)

    print("valid:\t", "\tmean", round(mean(all_num_valid), 1), ";\tmedian",
          round(median(all_num_valid), 1), ";\trange", min(all_num_valid), "to", max(all_num_valid))
    print("invalid:", "\tmean", round(mean(all_num_invalid), 1), ";\tmedian",
          round(median(all_num_invalid), 1), ";\trange", min(all_num_invalid), "to",
          max(all_num_invalid))
    print("cond inv:", "\tmean", round(mean(all_num_cond_invalid), 1), ";\tmedian",
          round(median(all_num_cond_invalid), 1), ";\trange", min(all_num_cond_invalid), "to",
          max(all_num_cond_invalid))
    print("all:\t", "\tmean", round(mean(all_num_exs), 1), ";\tmedian",
          round(median(all_num_exs), 1), ";\trange", min(all_num_exs), "to", max(all_num_exs))


if __name__ == '__main__':
    main()
