import argparse
import glob
import re
from typing import List

print_columns = ["name", "total_synthesis_time"]

regel_columns = ["regel_time", "regel_timeout", "regel_sketch", "regel_solution"]

all_columns = ["name", "enumerator", "timed_out", "total_synthesis_time", "regex_synthesis_time",
               "first_regex_time", "enumerated_regexes", "regex_interactions",
               "regex_distinguishing_time", "cap_groups_synthesis_time", "enumerated_cap_groups",
               "cap_conditions_synthesis_time", "enumerated_cap_conditions",
               "cap_conditions_interactions", "cap_conditions_distinguishing_time", "solution",
               "nodes", "first_regex", "cap_groups", "ground_truth", "regel_time", "regel_timeout",
               "regel_sketch", "regel_solution"]

exclude_instances = ["datetime2.txt", "date3.txt"]  # , "color.txt", "date.txt", "date7.txt", "id1.txt", "date3.txt"]

logs = {"nopruning": "log_10_22_mtnp", "dynamic": "log_10_28_dy",
        "multitree": "log_10_22_mt",
        "ktree": "log_10_22_kt", "lines": "log_10_22_li",
        "multi-dist": "log_10_26_muti-dist"}


class Instance:
    def __init__(self, name):
        global all_columns
        self.values = {}
        for col in all_columns:
            self.values[col] = "undefined"
        self.values['name'] = name


def print_table(instances: List, regel: bool):
    """ Print execution information for each instance (sorted by name) """
    global print_columns, regel_columns

    if regel:
        print_columns.extend(regel_columns)

    print(", ".join(print_columns))

    for idx, instance in enumerate(instances):
        row = []
        for col_name in print_columns:
            if col_name in ["solution", "cap_groups", "ground_truth", "regel_sketch", "regel_solution", "first_regex"]:
                row.append(f'"{instance.values[col_name]}"')
            else:
                row.append(str(instance.values[col_name]))
        print(', '.join(row))


def print_rank(instances):
    """ Print execution time for each instance (sorted by time) """
    ranked = sorted(instances,
                    key=lambda i: 4000 if i.values["total_synthesis_time"] == 'undefined' else
                    i.values["total_synthesis_time"])
    print("instance, time, ranking")
    for idx, instance in enumerate(ranked):
        time = 4000 if instance.values["total_synthesis_time"] == "undefined" else \
            instance.values["total_synthesis_time"]
        print(f'{instance.values["name"]}, {time}, {idx + 1}')


def print_regel_rank(instances):
    ranked = sorted(instances,
                    key=lambda i: 4000 if i.values["regel_time"] == 'undefined' else
                    i.values["regel_time"])
    print("instance, time, ranking")
    for idx, instance in enumerate(ranked):
        time = 4000 if instance.values["regel_time"] == "undefined" else instance.values["regel_time"]
        print(f'{instance.values["name"]}, {time}, {idx + 1}')


def print_compare_times():
    global logs
    instances = {}
    for log in logs:
        log_files = glob.glob(logs[log] + "/*.txt")
        instances[log] = []

        for log_file in log_files:
            instance = read_log(log_file)
            if instance is not None:
                instances[log].append(instance)

        instances[log] = sorted(instances[log], key=lambda i: i.values['name'])

    columns = list(logs.keys())
    print(", ".join(["instance"] + columns))
    # get number of instances from any list in the dictionary
    num_instances = len(next(iter(instances.values())))
    for idx in range(num_instances):
        row = []
        instance_name = next(iter(instances.values()))[idx].values["name"]
        row.append(instance_name)
        for c in columns:
            time = instances[c][idx].values["total_synthesis_time"]
            if time == "undefined":
                time = 4000
            row.append(time)
        print(", ".join(map(str, row)))


def print_count_solved(instances: List):
    count = 0
    for instance in instances:
        if instance.values["solution"] != 'No solution' and instance.values["solution"] != 'undefined':
            count += 1
    print(count)


def print_count_solved_all(instances: List):
    instances = list(filter(lambda i: i.values["solution"] != 'No solution'
                                      and i.values["solution"] != 'undefined', instances))
    count_3600 = 0
    count_60 = 0
    count_10 = 0
    for instance in instances:
        if instance.values["first_regex_time"] < 3600:
            count_3600 += 1
        if instance.values["first_regex_time"] < 60:
            count_60 += 1
        if instance.values["first_regex_time"] < 10:
            count_10 += 1
    print(count_10, count_60, count_3600)


def print_count_not_timeout(instances: List):
    count = 0
    for instance in instances:
        if not instance.values['timed_out']:
            count += 1
    print(count)


def print_count_not_timeout_all(instances: List):
    instances = list(filter(lambda i: not i.values['timed_out'], instances))
    count_3600 = 0
    count_60 = 0
    count_10 = 0
    for instance in instances:
        if instance.values["total_synthesis_time"] < 3600:
            count_3600 += 1
        if instance.values["total_synthesis_time"] < 60:
            count_60 += 1
        if instance.values["total_synthesis_time"] < 10:
            count_10 += 1
    print(count_10, count_60, count_3600)


def print_regel_count_not_timeout_all(instances):
    instances = list(filter(lambda i: not i.values['regel_timeout'], instances))
    count_3600 = 0
    count_60 = 0
    count_10 = 0
    for instance in instances:
        if instance.values["regel_time"] < 3600:
            count_3600 += 1
        if instance.values["regel_time"] < 60:
            count_60 += 1
        if instance.values["regel_time"] < 10:
            count_10 += 1
    print(count_10, count_60, count_3600)




def main():
    parser = argparse.ArgumentParser(description='Validations Synthesizer tester',
                                     formatter_class=argparse.ArgumentDefaultsHelpFormatter)
    parser.add_argument('log_dir', metavar='DIR', type=str, help="Logs directory", default='')
    parser.add_argument('-r', '--regel-log-dir', metavar='DIR', type=str,
                        help="Regel logs directory", default='')
    parser.add_argument('--rank', action="store_true", help="Rank instances according to synthesis time")
    parser.add_argument('--count-solved', action="store_true",
                        help="Count number of instances that returned a solution (time out or not).")
    parser.add_argument('--count-solved-all', action="store_true",
                        help="Count number of instances that returned a solution (time out or not) in 10, 60 and 3600 "
                             "seconds.")
    parser.add_argument('--count-not-timeout', action="store_true",
                        help="Count number of instances that did not time out.")
    parser.add_argument('--count-not-timeout-all', action="store_true",
                        help="Count number of instances that did not time out in 10, 60 and 3600 seconds.")
    parser.add_argument('--regel-count-not-timeout-all', action="store_true",
                        help="Count number of instances that did not time out with REGEL in 10, 60 and 3600 seconds.")
    parser.add_argument('--rank-regel', action="store_true", help="Make REGEL time ranking")
    parser.add_argument('--compare-times', action="store_true",
                        help="Make table comparing the synthesis time for different methods")

    args = parser.parse_args()

    log_dir = args.log_dir
    regel_log_dir = args.regel_log_dir

    log_files = glob.glob(log_dir + "/*.txt")
    instances = []

    for log_file in log_files:
        instance = read_log(log_file)
        if instance is not None:
            instances.append(instance)

    if len(regel_log_dir) > 0:
        for instance in instances:
            read_regel_log(instance, regel_log_dir)

    instances = sorted(instances, key=lambda i: i.values['name'])

    if args.rank:
        print_rank(instances)
    elif args.rank_regel:
        assert len(regel_log_dir) > 0, "please indicate REGEL logs directory"
        print_regel_rank(instances)
    elif args.compare_times:
        print_compare_times()
    elif args.count_solved:
        print_count_solved(instances)
    elif args.count_solved_all:
        print_count_solved_all(instances)
    elif args.count_not_timeout:
        print_count_not_timeout(instances)
    elif args.count_not_timeout_all:
        print_count_not_timeout_all(instances)
    elif args.regel_count_not_timeout_all:
        assert len(regel_log_dir) > 0, "please indicate REGEL logs directory"
        print_regel_count_not_timeout_all(instances)
    else:
        print_table(instances, len(regel_log_dir) > 0)


def read_regel_log(instance, regel_log_dir):
    try:
        with open(regel_log_dir + "/" + instance.values['name'] + "-1") as f:
            for line in f:
                if "Sketch" in line:
                    regex = r"Sketch: (.+)"
                    m = re.search(regex, line)
                    if m is not None:
                        instance.values["regel_sketch"] = m[1]
                elif "Learned program" in line:
                    regex = r"Learned program: (.+): (?:\d+\.\d+)"
                    m = re.search(regex, line)
                    if m is not None:
                        instance.values["regel_solution"] = m[1]
                elif "Total time" in line:
                    regex = r"Total time: (\d+\.\d+)"
                    m = re.search(regex, line)
                    if m is not None:
                        instance.values['regel_time'] = float(m[1])
                        instance.values['regel_timeout'] = False
    except IOError:
        try:
            with open(regel_log_dir + "/" + instance.values['name'] + "-b") as f:
                for line in f:
                    if "Learned program" in line:
                        regex = r"Learned program: (.+): (?:\d+\.\d+)"
                        m = re.search(regex, line)
                        if m is not None:
                            instance.values["regel_solution"] = m[1]
                    elif "Total time" in line:
                        regex = r"Total time: (\d+\.\d+)"
                        m = re.search(regex, line)
                        if m is not None:
                            instance.values['regel_time'] = float(m[1])
                            instance.values['regel_timeout'] = False
        except IOError:
            print("could not open", regel_log_dir + "/" + instance.values['name'] + "-1")


def read_log(log_file):
    instance_name = list(filter(None, log_file.split('/')))[-1]
    for excluded in exclude_instances:
        if excluded in instance_name:
            return None
    instance = Instance(instance_name)
    with open(log_file) as f:
        regex_synthesis = False
        cap_groups_synthesis = False
        cap_conditions_synthesis = False
        solution_print = False
        for line in f:
            if "Enumerator" in line:
                regex = "Enumerator: (.+)"
                m = re.search(regex, line)
                if m is not None:
                    instance.values['enumerator'] = m[1]
            elif "Terminated" in line:
                regex = "Terminated: (.+)"
                m = re.search(regex, line)
                if m is not None:
                    instance.values['timed_out'] = m[1] == 'True'
            elif "Elapsed time" in line:
                regex = r"Elapsed time: (\d+\.\d+)"
                m = re.search(regex, line)
                if m is not None:
                    instance.values['total_synthesis_time'] = float(m[1])
            elif "Time per depth" in line:
                regex = "Time per depth: (.+)"
                m = re.search(regex, line)
                if m is not None:
                    instance.values['per_depth_times'] = m[1]
            elif "Regex synthesis" in line:
                regex_synthesis = True
                continue
            elif "Capturing groups synthesis" in line:
                regex_synthesis = False
                cap_groups_synthesis = True
                continue
            elif "Capturing conditions synthesis" in line:
                cap_groups_synthesis = False
                cap_conditions_synthesis = True
                continue
            elif "First regex:" in line:
                regex = r"First regex: (.+)"
                m = re.search(regex, line)
                if m is not None:
                    instance.values['first_regex'] = m[1]
            elif "Solution" in line:
                cap_conditions_synthesis = False
                solution_print = True
                regex = r"Solution: (.+)"
                m = re.search(regex, line)
                if m is not None:
                    instance.values['solution'] = m[1]
                continue
            elif "No solution" in line:
                cap_conditions_synthesis = False
                solution_print = True
                instance.values['solution'] = 'No solution'
                instance.values['cap_groups'] = None
                continue

            elif regex_synthesis:
                if "Regex time" in line:
                    regex = r"Regex time: (\d+\.\d+)"
                    m = re.search(regex, line)
                    if m is not None:
                        instance.values['regex_synthesis_time'] = float(m[1])
                elif "First regex time" in line:
                    regex = r"First regex time: (\d+\.\d+)"
                    m = re.search(regex, line)
                    if m is not None:
                        instance.values['first_regex_time'] = float(m[1])
                elif "Enumerated" in line:
                    regex = r"Enumerated: (\d+)"
                    m = re.search(regex, line)
                    if m is not None:
                        instance.values['enumerated_regexes'] = int(m[1])
                elif "Interactions" in line:
                    regex = r"Interactions: (\d+)"
                    m = re.search(regex, line)
                    if m is not None:
                        instance.values['regex_interactions'] = int(m[1])
                elif "Distinguish time" in line:
                    regex = r"Distinguish time: (\d+\.\d+)"
                    m = re.search(regex, line)
                    if m is not None:
                        instance.values['regex_distinguishing_time'] = float(m[1])

            elif cap_groups_synthesis:
                if "Cap. groups time" in line:
                    regex = r"Cap. groups time: (\d+\.\d+)"
                    m = re.search(regex, line)
                    if m is not None:
                        instance.values['cap_groups_synthesis_time'] = float(m[1])
                elif "Enumerated" in line:
                    regex = r"Enumerated: (\d+)"
                    m = re.search(regex, line)
                    if m is not None:
                        instance.values['enumerated_cap_groups'] = int(m[1])

            elif cap_conditions_synthesis:
                if "Cap. conditions time" in line:
                    regex = r"Cap. conditions time: (\d+\.\d+)"
                    m = re.search(regex, line)
                    if m is not None:
                        instance.values['cap_conditions_synthesis_time'] = float(m[1])
                elif "Enumerated" in line:
                    regex = r"Enumerated: (\d+)"
                    m = re.search(regex, line)
                    if m is not None:
                        instance.values['enumerated_cap_conditions'] = int(m[1])
                elif "Interactions" in line:
                    regex = r"Interactions: (\d+)"
                    m = re.search(regex, line)
                    if m is not None:
                        instance.values['cap_conditions_interactions'] = int(m[1])
                elif "Distinguish time" in line:
                    regex = r"Distinguish time: (\d+\.\d+)"
                    m = re.search(regex, line)
                    if m is not None:
                        instance.values['cap_conditions_distinguishing_time'] = float(m[1])

            elif solution_print:
                if "Nodes" in line:
                    regex = r"Nodes: (\d+)"
                    m = re.search(regex, line)
                    if m is not None:
                        instance.values['nodes'] = int(m[1])
                elif "No capturing groups" in line:
                    instance.values['cap_groups'] = None
                elif "Cap. groups" in line:
                    regex = r"Cap\. groups: (.+)"
                    m = re.search(regex, line)
                    if m is not None:
                        instance.values['cap_groups'] = m[1]
                elif "Num. cap. groups" in line:
                    regex = r"Num\. cap\. groups: (\d+)"
                    m = re.search(regex, line)
                    if m is not None:
                        instance.values['num_cap_groups'] = m[1]
                elif "Ground truth" in line:
                    regex = r"Ground truth: (.+)"
                    m = re.search(regex, line)
                    if m is not None:
                        instance.values['ground_truth'] = m[1]

    return instance


if __name__ == '__main__':
    main()
