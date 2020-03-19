import re


def parse_file(filename):
    valid_exs = []
    invalid_exs = []
    with open(filename, "r") as in_file:
        next_line = in_file.readline()
        while next_line and not next_line.startswith("++"):
            next_line = in_file.readline()

        next_line = in_file.readline()  # skip line with "++"
        while next_line and not next_line.startswith("--"):
            next_line = next_line.rstrip()
            if len(next_line) > 0:
                if "AlphaRegex" not in filename:
                    valid_exs.append([i.strip() for i in next_line.split(',')])
                else:
                    if 'X' not in next_line:
                        valid_exs.append([next_line])
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
                                valid_exs.append([new0])
                                valid_exs.append([new1])
            next_line = in_file.readline()

        next_line = in_file.readline()  # skip line with "--"
        while next_line:
            next_line = next_line.rstrip()
            if len(next_line) > 0:
                if "AlphaRegex" not in filename:
                    invalid_exs.append([i.strip() for i in next_line.split(',')])
                else:
                    if 'X' not in next_line:
                        invalid_exs.append([next_line])
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
                                invalid_exs.append([new0])
                                invalid_exs.append([new1])
            next_line = in_file.readline()

    return valid_exs, invalid_exs