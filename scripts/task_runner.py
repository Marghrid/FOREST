import datetime
import glob
import random
import socket
import subprocess
import time

from termcolor import colored

all_methods = ('multitree', 'ktree', 'lines', 'dynamic')
MAXSIGTERMS = 10


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

    def __str__(self):
        return self.name


class Task:
    def __init__(self, command, instance, timeout):
        self.command = command
        self.instance = instance
        self.process = None
        self.start_time = 0
        self.timeout = timeout

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
        global MAXSIGTERMS
        count = 0
        while self.process.poll() is None and count < MAXSIGTERMS:
            self.process.terminate()
            time.sleep(2)
            count += 1
        print(f"Sent SIGTERM x {count}.")
        if self.process.poll() is None:
            print("Sending SIGKILL.")
            self.process.kill()

    def is_done(self):
        """ Checks if task is done or has timed out. """
        elapsed = time.time() - self.start_time
        if elapsed >= self.timeout:
            print(colored(f"{self.instance} timed out.", "red"))
            self.terminate()
            return True
        return self.process.poll() is not None

    def wait(self):
        print(colored(f"Waiting {self.timeout}s for {self.instance}.", "cyan"))
        try:
            self.process.wait(timeout=self.timeout)
        except subprocess.TimeoutExpired:
            print(colored(f"{self.instance} timed out.", "red"))
            self.terminate()
            return

    def manage_output(self, show_output):
        po, pe = self.process.communicate()
        po = str(po, encoding='utf-8').splitlines()
        pe = str(pe, encoding='utf-8').splitlines()

        if self.process.returncode != 0:
            print(colored(f"RETURN CODE {self.instance}: "
                          f"{self.process.returncode}", "red"))
        for line in pe + po:
            if show_output:
                print(" ", line)


class TaskRunner:
    def __init__(self, instance_dirs, method='multitree', no_pruning=False,
                 sketching='none', num_processes=1, timeout=120, show_output=False,
                 resnax=False, max_valid=-1, max_invalid=-1, solve_only=-1, logs_dir=''):
        self.show_output = show_output
        self.timeout = timeout + 2
        self.tasks = []
        self.instances = []
        self.num_processes = num_processes
        self.poll_time = min(30, self.timeout // 15)
        self.no_pruning = no_pruning
        self.logs_dir = logs_dir
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
        if sketching != 'none':
            command_base.append('--sketch')
            command_base.append(sketching)

        if len(logs_dir) > 0:
            command_base.extend(['-l', logs_dir])

        command_base.append("-e")

        now = datetime.datetime.now()
        print(f"Running on {socket.gethostname()}, "
              f"starting on {now.strftime('%Y-%m-%d %H:%M:%S')}, "
              f"using {methods}.")

        for instance_dir in instance_dirs:
            instance_paths = glob.glob(instance_dir + "/*.txt")

            for inst_path in instance_paths:
                inst_name = inst_path.split("/")[-1]
                inst_name = inst_name.replace(".txt", "", 1)
                self.instances.append(Instance(inst_name, inst_path))

        # sort instances by name
        print(colored(f"Found {len(self.instances)} instances.", "magenta"))

        if 0 < solve_only < len(self.instances):
            random.seed("regex" + str(solve_only))
            self.instances = random.sample(self.instances, solve_only)
            print(colored(f"Selected {len(self.instances)} instances.", "magenta"))

        self.instances = sorted(self.instances, key=lambda i: i.name)

        # create tasks:
        for inst in self.instances:
            for m in methods:
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

    def run(self):
        """ Starts running tasks in random order """
        if self.num_processes == 1:
            self.run_sequentially()
            return
        half_true_iter = half_true()
        start_time = time.time()
        while len(self.to_run) > 0 or len(self.running) > 0:
            to_remove = []
            for task in self.running:
                if task.is_done():
                    task.manage_output(self.show_output)
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

    def run_sequentially(self):
        start_time = time.time()
        while len(self.to_run) > 0:
            new_task = self.to_run.pop()
            self.running = [new_task]
            new_task.run()
            new_task.wait()
            new_task.manage_output(self.show_output)
            self.running = []
            print(colored(
                f"{len(self.tasks) - len(self.to_run) - len(self.running)} done, "
                f"{len(self.to_run) + len(self.running)} to go. "
                f"Elapsed {nice_time(time.time() - start_time)}.", "magenta"))

    def terminate_all(self):
        print(colored("Terminating all tasks", "red"))
        self.to_run = []
        while len(self.running) > 0:
            task = self.running.pop()
            task.terminate()
