def parse_file(filename):
    invalid_exs = []
    valid_exs = []
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
        while next_line:
            next_line = next_line.rstrip()
            exs = read_example(filename, next_line)
            invalid_exs.extend(exs)
            next_line = in_file.readline()

    return valid_exs, invalid_exs


def read_example(filename, next_line):
    exs = []
    if len(next_line) > 0:
        if "AlphaRegex" not in filename:
            exs = [[i.strip() for i in next_line.split(',')]]
        else:
            exs = read_AlphaRegex_example(next_line)
    return exs


def read_AlphaRegex_example(next_line):
    exs = []
    if 'X' not in next_line:
        exs.append([next_line])
    else:
        with_x = [next_line]
        while len(with_x) > 0:
            n = with_x.pop(0)
            new0 = n.replace("X", "0", 1)
            new1 = n.replace("X", "1", 1)
            if "X" in new0:
                with_x.append(new0)
                with_x.append(new1)
            else:
                exs.append([new0])
                exs.append([new1])
    return exs