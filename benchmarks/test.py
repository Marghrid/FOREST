import glob, os, re


def is_regex(next_line: str):
    if len(next_line) == 0:
        return False
    try:
        re.compile(next_line)
        return True
    except re.error:
        return False


def read_example(filename, next_line):
    exs = []
    if len(next_line) > 0:
        if "AlphaRegex" not in filename:
            exs = [[i.strip() for i in next_line.split(',')]]
        else:
            exs = read_AlphaRegex_example(next_line)
    return exs


def parse_file(filename):
    invalid_exs = []
    valid_exs = []
    ground_truth = ''
    with open(filename, "r") as in_file:

        next_line = in_file.readline()
        while next_line and not next_line.startswith("++"):
            next_line = in_file.readline()

        next_line = in_file.readline()  # skip line with "++"
        while next_line and not next_line.startswith("--"):
            next_line = next_line.rstrip()
            exs = read_example(filename, next_line)
            valid_exs.extend(exs)
            next_line = in_file.readline()

        next_line = in_file.readline()  # skip line with "--"
        while next_line and not next_line.startswith("**"):
            next_line = next_line.rstrip()
            exs = read_example(filename, next_line)
            invalid_exs.extend(exs)
            next_line = in_file.readline()

        while next_line:
            next_line = next_line.rstrip()
            if is_regex(next_line):
                ground_truth = next_line
                break
            next_line = in_file.readline()

    return valid_exs, invalid_exs, ground_truth


for file in glob.glob("*.txt"):
    pos = False
    neg = False
    gt = False
    with open(file) as f:
        for line in f:
            if line.startswith('++'):
                pos = True
            elif line.startswith('--'):
                neg = True
            elif line.startswith('**'):
                gt = True
            if gt and is_regex(line):
                ground_truth = line
                break
    if not (pos and neg and gt):
        print(file, "Does not have all parts")
        exit()
    else:
        print(file, "parts ok")
        v, i, g = parse_file(file)
    if len(g) < 1:
        print(file, "invalid ground truth", f"'{g}'")
        exit()

    for vx in v:
        match = re.fullmatch(g, vx[0])
        if not match:
            print(f"'{g}'", "does not match", vx[0])
            exit()
    for ix in i:
        match = re.fullmatch(g, ix[0])
        if match:
            print(f"'{g}'", "matches", ix[0])
            exit()
print("all good.")
