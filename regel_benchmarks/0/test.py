import glob, os, re, time

def less_than(s1, s2):
    if len(s1) < len(s2):
        return True
    elif len(s1) == len(s2):
        return s1 < s2
    else:
        return False

def is_regex(next_line: str):
    if len(next_line) == 0:
        return False
    try:
        re.compile(next_line)
        return True
    except re.error:
        return False

def read_resnax_example(next_line):
    match = re.fullmatch(r'"(.*)",([+\-])', next_line)
    if match is None:
        return None, None

    ex = match.groups()[0]
    valid = match.groups()[1] == '+'
    return ex, valid

def parse_resnax(filename):
    invalid_exs = []
    valid_exs = []
    ground_truth_next = False
    ground_truth = ''
    with open(filename, "r") as in_file:
        for next_line in in_file:
            next_line = next_line.rstrip()
            if ground_truth_next:
                ground_truth = next_line
                ground_truth_next = False
                continue
            ex, valid = read_resnax_example(next_line)
            if ex is None:
                if next_line.startswith('// gt') or next_line.startswith('// ground truth'):
                    ground_truth_next = True
                continue
            if valid:
                valid_exs.append([ex])
            else:
                invalid_exs.append([ex])

    return valid_exs, invalid_exs, ground_truth

for file in sorted(glob.glob("*.txt"), key=lambda s: s.rjust(9, '0')):
    pos = False
    neg = False
    gt = False
    input("next?")
    print('\n',file)
    v, i, g = parse_resnax(file)
    print(v)
    print(i)
    print(g)
    if  not is_regex(g):
        print("invalid ground truth", f"'{g}'")
        continue

    for vx in v:
        match = re.fullmatch(g, vx[0])
        if not match:
            print(f"'{g}'", "does not match", vx[0])
            continue
    for ix in i:
        match = re.fullmatch(g, ix[0])
        if match:
            print(f"'{g}'", "matches", ix[0])
            continue
    print("all good.")
