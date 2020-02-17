import glob
import subprocess

instances = []
for file in glob.glob("instances/strings/*.txt"):
    instances.append(file)
commands = [["runsolver", "-W", "60", "python3", "validate.py", "-f", instance] for instance in instances]

processes = []

instance_times = {}

for command in commands:
    times = []
    print("\n=====  " + command[-1] + "  =====")
    for i in range(4):
        process = subprocess.Popen(command, stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        process.wait()

        po, pe = process.communicate()
        po = str(po, encoding ='utf-8').splitlines()
        pe = str(pe, encoding ='utf-8').splitlines()
        for l in po + pe:
            if "Real time" in l:
                time = l.replace("Real time (s):", " ", 1)
                time = float(time)
                times.append(time)
                print(time, "s")
    avg_time = sum(times) / len(times)
    print("avg time:", avg_time, "s")
    instance_times[command[-1]] = avg_time

print(instance_times)
