import argparse
import glob

# noinspection PyTypeChecker
from dataclasses import dataclass
from operator import add
from statistics import median, mean

from synth_regex import show
from forest.parse_examples import parse_resnax, parse_file


@dataclass
class InstanceStats:
    name: str
    path: str
    num_valid: int
    num_invalid: int


def main():
    parser = argparse.ArgumentParser(description='Validations Synthesizer tester',
                                     formatter_class=argparse.ArgumentDefaultsHelpFormatter)
    parser.add_argument('directories', type=str, metavar="dir", nargs='+',
                        help='Directories with instances')
    parser.add_argument('--resnax', action='store_true',
                        help='read resnax i/o examples format.')
    args = parser.parse_args()

    instances = []



    for dir in args.directories:
        instance_paths = glob.glob(dir + "/*.txt")
        instances.extend(instance_paths)



    instance_stats = []
    for instance in instances:
        if args.resnax:
            valid, invalid, ground_truth = parse_resnax(instance)
        else:
            valid, invalid, ground_truth = parse_file(instance)

        show(valid, invalid, ground_truth)

        inst_name = instance.split("/")[-1]
        inst_name = inst_name.replace(".txt", "", 1)

        new_stat = InstanceStats(inst_name, instance, len(valid), len(invalid))
        instance_stats.append(new_stat)

    all_num_valid = list(map(lambda s: s.num_valid, instance_stats))
    all_num_invalid = list(map(lambda s: s.num_invalid, instance_stats))
    all_num_exs = list(map(add, all_num_valid, all_num_invalid))

    print("Total instances:", len(instance_stats))

    print("mean num valid:", mean(all_num_valid))
    print("mean num invalid:", mean(all_num_invalid))
    print("median num valid:", median(all_num_valid))
    print("median num invalid:", median(all_num_invalid))

    print("mean total:", mean(all_num_exs))
    print("median total:", median(all_num_exs))


if __name__ == '__main__':
    main()
