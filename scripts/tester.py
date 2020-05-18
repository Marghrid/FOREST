import datetime
import glob
import re
import socket
import subprocess
import time

from termcolor import colored

all_methods = ('multitree', 'ktree', 'lines', 'funny')


def half_true():
    n = 0
    while True:
        yield n % 4 == 0
        n += 1


def nice_time(seconds):
    seconds = round(seconds)
    m, s = divmod(seconds, 60)
    h, m = divmod(m, 60)
    ret = ''
    if h > 0:
        ret += f'{h}h'
    if m > 0:
        ret += f'{m}m'
    ret += f'{s}s'
    return ret


class Instance:
    def __init__(self, name, path):
        self.name = name
        self.path = path
        self.tasks = []

    def add_task(self, task):
        self.tasks.append(task)

    def terminate_tasks(self):
        for t in self.tasks:
            t.terminate()

    def __str__(self):
        return self.name


class Task:
    def __init__(self, command, instance, timeout):
        self.command = command
        self.instance = instance
        self.instance.add_task(self)
        self.timeout = timeout
        self.timed_out = False
        self.process = None
        self.start_time = 0
        self.time = -1
        self.first_time = -1
        self.enumerator = 'Enumerator'
        self.enumerated = -1
        self.interactions = -1
        self.nodes = -1
        self.solution = 'Solution'
        self.ground_truth = 'Ground truth'

        enc_idx = self.command.index('-e')
        self.encoding = self.command[enc_idx + 1]

    def run(self):
        print(colored(f"Running {self.instance} {self.encoding}: "
                      f"{' '.join(self.command)}", "blue"))
        self.process = subprocess.Popen(self.command,
                                        stdout=subprocess.PIPE,
                                        stderr=subprocess.PIPE)
        self.start_time = time.time()

    def terminate(self):
        while self.process.poll() is None:
            self.process.terminate()
            print("Sending SIGTERM...", end=" ")
            time.sleep(2)
        print(".")

    def is_done(self):
        """ Checks if task is done or has timed out. """
        elapsed = time.time() - self.start_time
        if elapsed >= self.timeout:
            print(colored(f"{self.instance} timed out.", "red"))
            self.terminate()
            self.timed_out = True
            return True
        return self.process.poll() is not None

    def wait(self):
        print(colored(f"Waiting {self.timeout}s for {self.instance}.", "cyan"))
        try:
            self.process.wait(timeout=self.timeout)
        except subprocess.TimeoutExpired:
            print(colored(f"{self.instance} timed out.", "red"))
            self.terminate()
            self.timed_out = True
            return

    def read_output(self, show_output):
        po, pe = self.process.communicate()
        po = str(po, encoding='utf-8').splitlines()
        pe = str(pe, encoding='utf-8').splitlines()

        if self.process.returncode != 0:
            print(colored(f"RETURN CODE {self.instance}: "
                          f"{self.process.returncode}", "red"))

        end = False
        first = False
        for l in pe:
            print(colored("ERROR: " + l, "red"))
        for l in po:
            # print(l)
            # if re.search("[\w+]", l) is not None and show_output:
            if show_output:
                print(" ", l)
            if not end:
                if "Synthesizer done" in l:
                    end = True
                if "Program accepted" in l and not first:
                    m = re.search("Program accepted.*(\d+\.\d+) seconds", l)
                    if m is not None:
                        self.first_time = float(m.groups()[0])
                    else:
                        print("Somethong went wrong")
                    first = True

            else:
                if "Elapsed time" in l:
                    regex = r"Elapsed time: (\d+\.\d+)"
                    m = re.search(regex, l)
                    if m is not None:
                        self.time = float(m[1])
                if "Enumerator" in l:
                    regex = r"Enumerator: (.+)"
                    m = re.search(regex, l)
                    if m is not None:
                        self.enumerator = m[1]
                if "Enumerated" in l:
                    regex = r"Enumerated: (\d+)"
                    m = re.search(regex, l)
                    if m is not None:
                        self.enumerated = int(m[1])
                if "Interactions" in l:
                    regex = r"Interactions: (\d+)"
                    m = re.search(regex, l)
                    if m is not None:
                        self.interactions = int(m[1])
                if "Nodes" in l:
                    regex = r"Nodes: (\d+)"
                    m = re.search(regex, l)
                    if m is not None:
                        self.nodes = int(m[1])
                if "[info]   Solution: " in l:
                    self.solution = l.replace("[info]   Solution: ", "", 1)
                if "No solution" in l:
                    self.solution = "No solution"
                if "Ground truth:" in l:
                    self.ground_truth = l.replace("[info]   Ground truth: ", "", 1)


class Tester:
    def __init__(self, instance_dirs, method='multitree', no_pruning=False,  num_processes=1, run_each=1,
                 timeout=120, show_output=False, resnax=False, max_valid=-1,
                 max_invalid=-1):
        self.show_output = show_output
        self.timeout = timeout + 2
        self.tasks = []
        self.instances = []
        self.num_processes = num_processes
        self.poll_time = min(30, self.timeout // 15)
        self.no_pruning = no_pruning
        if method == 'compare-times':
            methods = all_methods
        else:
            methods = [method]

        command_base = ["python3", "-O", "synth_regex.py", '-s']
        if max_valid > 0:
            command_base += ["-v", str(max_valid)]
        if max_invalid > 0:
            command_base += ["-i", str(max_invalid)]
        if no_pruning:
            command_base.append('--no-pruning')
        if resnax:
            command_base.append('--resnax')

        command_base.append("-e")

        now = datetime.datetime.now()
        print(f"Running on {socket.gethostname()}, "
              f"starting on {now.strftime('%Y-%m-%d %H:%M:%S')}, "
              f"using {methods}.")

        for dir in instance_dirs:
            instance_paths = glob.glob(dir + "/*.txt")

            for inst_path in instance_paths:
                inst_name = inst_path.split("/")[-1]
                inst_name = inst_name.replace(".txt", "", 1)
                self.instances.append(Instance(inst_name, inst_path))

        # sort instances by name
        print(colored(f"Found {len(self.instances)} instances.", "magenta"))
        self.instances = sorted(self.instances, key=lambda i: i.name)

        # create tasks:
        for inst in self.instances:
            for m in methods:
                for i in range(run_each):
                    command = command_base + [m] + [inst.path]
                    new_task = Task(command=command, instance=inst, timeout=self.timeout)
                    self.tasks.append(new_task)

        print(colored(f"Created {len(self.tasks)} tasks.", "magenta"))
        print(colored(f"Polling every {self.poll_time} seconds.", "magenta"))

        # tasks are ordered randomly
        self.to_run = self.tasks.copy()
        # random.shuffle(self.to_run)

        # currently running tasks
        self.running = []

    def test(self):
        """ Starts running tasks in random order """
        if self.num_processes == 1:
            self.test_sequentially()
            return
        half_true_iter = half_true()
        start_time = time.time()
        while len(self.to_run) > 0 or len(self.running) > 0:
            to_remove = []
            for task in self.running:
                if task.is_done():
                    task.read_output(self.show_output)
                    to_remove.append(task)
            for t in to_remove:
                self.running.remove(t)

            while len(self.running) < self.num_processes:
                if len(self.to_run) == 0:
                    break
                new_task = self.to_run.pop()
                self.running.append(new_task)
                new_task.run()
            if next(half_true_iter):
                print(colored(
                    f"{len(self.tasks) - len(self.to_run) - len(self.running)} done, "
                    f"{len(self.to_run) + len(self.running)} to go. "
                    f"Elapsed {nice_time(time.time() - start_time)}.", "magenta"))
            time.sleep(self.poll_time)

    def test_sequentially(self):
        start_time = time.time()
        while len(self.to_run) > 0:
            new_task = self.to_run.pop()
            self.running = [new_task]
            new_task.run()
            new_task.wait()
            new_task.read_output(self.show_output)
            self.running = []
            print(colored(
                f"{len(self.tasks) - len(self.to_run) - len(self.running)} done, "
                f"{len(self.to_run) + len(self.running)} to go. "
                f"Elapsed {nice_time(time.time() - start_time)}.", "magenta"))

    def print_results(self):
        """ Print execution information for each instance (sorted by name) """
        maxl = max(map(lambda i: len(i.name), self.instances)) + 2
        max_enumerators_length = max(map(lambda t: len(t.enumerator), self.tasks)) + 2
        max_enumerated_length = max(map(lambda t: len(str(t.enumerated)), self.tasks)) + 2
        now = datetime.datetime.now()
        print(
            f"\n =====  RESULTS on {socket.gethostname()}, {now.strftime('%Y-%m-%d %H:%M:%S')} ===== ")
        print(
            "instance, time, first-time, interactions, enumerator, enumerated, timed-out, nodes, solution, ground-truth")
        for inst in self.instances:
            times = list(map(lambda t: t.time, inst.tasks))
            first_times = list(map(lambda t: t.first_time, inst.tasks))
            enumerated = list(map(lambda t: t.enumerated, inst.tasks))
            enumerators = list(map(lambda t: t.enumerator, inst.tasks))
            interactions = list(map(lambda t: t.interactions, inst.tasks))
            nodes = list(map(lambda t: t.nodes, inst.tasks))
            timed_out = list(map(lambda t: t.timed_out, inst.tasks))

            # times = list(filter(lambda x: x >= 0, times))
            # enumerated = list(filter(lambda x: x > 0, enumerated))
            # interactions = list(filter(lambda x: x >= 0, interactions))

            if not all(map(lambda x: x >= 0, times)):
                print(f"{inst.name},".ljust(maxl), "error")
            # assert all(map(lambda x: x > 0, enumerated))
            # assert all(map(lambda x: x >= 0, interactions))

            if not len(times) == len(enumerated) == len(enumerators) == len(interactions):
                print("different lengths")

            if len(times) == 0:
                print(f"{inst.name},".ljust(maxl), "timed out")
                continue
            if any(map(lambda x: x != enumerated[0], enumerated)):
                print(f"{inst.name}:".ljust(maxl),
                      "does not always enumerate the same number of programs")
            if any(map(lambda x: x != enumerators[0], enumerators)):
                print(f"{inst.name}:".ljust(maxl),
                      "does not always use the same enumerator")
            if any(map(lambda x: x != interactions[0], interactions)):
                print(f"{inst.name}:".ljust(maxl), "has different number of interactions")
            if any(map(lambda x: x != nodes[0], nodes)):
                print(f"{inst.name}:".ljust(maxl), "has different number of nodes")
            if any(map(lambda x: x != timed_out[0], timed_out)):
                print(f"{inst.name}:".ljust(maxl), "has different timed_out")
            else:
                print(f"{inst.name},".ljust(maxl),
                      f"{round(sum(times) / len(times), 2)},".ljust(10),
                      f"{round(sum(first_times) / len(first_times), 2)},".ljust(10),
                      f"{interactions[0]},".ljust(3),
                      f"{enumerators[0]},".ljust(max_enumerators_length),
                      f"{enumerated[0]},".ljust(max_enumerated_length),
                      f"{int(timed_out[0])},",
                      f"{nodes[0]},".ljust(3),
                      f'"{inst.tasks[0].solution}",',
                      f'"{inst.tasks[0].ground_truth}"')

    def print_time_comparison(self):
        maxl = max(map(lambda i: len(i.name), self.instances)) + 2
        print(f"instance,".ljust(maxl), end='')
        for m in all_methods:
            print(f"{m},", end='')
        print()
        for inst in self.instances:
            print(f"{inst.name},".ljust(maxl), end='')
            for m in all_methods:
                # check that all methods have tasks.
                assert any(map(lambda t: t.encoding == m, inst.tasks))
                m_tasks = list(filter(lambda t: t.encoding == m, inst.tasks))
                times = map(lambda t: t.time, m_tasks)
                times = list(filter(lambda x: x >= 0, times))

                if len(times) == 0:
                    print(f"timeout,".ljust(9), end='')
                    continue
                else:
                    print(f"{round(sum(times) / len(times), 2)},".ljust(9), end='')
            print()

    def terminate_all(self):
        print(colored("Terminating all tasks", "red"))
        self.to_run = []
        while len(self.running) > 0:
            task = self.running.pop()
            task.terminate()
