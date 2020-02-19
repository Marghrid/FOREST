import glob
import re
import subprocess

instances = []
for file in glob.glob("instances/strings/*.txt"):
    instances.append(file)
commands = [["runsolver", "-W", "60", "python3", "validate.py", "-f", instance] for instance in instances]
processes = []
instance_times = {}

for command in commands:
    times = []
    instructions = []
    print("\n=====  " + command[-1] + "  =====")
    for i in range(4):
        process = subprocess.Popen(command, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        processes.append(process)
    
    for process in processes:
        process.wait()
        po, pe = process.communicate()
        po = str(po, encoding ='utf-8').splitlines()
        pe = str(pe, encoding ='utf-8').splitlines()
        time = -1
        enumerated = -1
        for l in po + pe:
            if "Maximum wall clock time exceeded:" in l:
                print("timeout")
                break
            if "Real time" in l:
                time = l.replace("Real time (s):", " ", 1)
                time = float(time)
            if "attempts" in l:
                regex = "(\\d+) attempts"
                bla = int(re.search(regex, l)[1])
                enumerated = bla
        times.append(time)
        print(time, "s")
        print("enumerated", bla)

    processes = []
    if len(times) > 0:
        avg_time = sum(times) / len(times)
    else:
        avg_time = -1
    print("avg time:", avg_time, "s")
    instance_times[command[-1]] = avg_time

print("\n===== Final =====")
for i in instance_times:
    print(i, ",", "{0:.2f}".format(instance_times[i]))

