from tyrell.decider import Example


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
                valid_exs.append([i.strip() for i in next_line.split(',')])
            next_line = in_file.readline()

        next_line = in_file.readline()  # skip line with "--"
        while next_line:
            next_line = next_line.rstrip()
            if len(next_line) > 0:
                invalid_exs.append([i.strip() for i in next_line.split(',')])
            next_line = in_file.readline()

    # if len(valid_exs) < 1:
    #     new_ex = input("Please enter a valid example for the form:")
    #     valid_exs.append(new_ex)
    # if len(invalid_exs) < 1:
    #     new_ex = input("Please enter a invalid example for the form:")
    #     invalid_exs.append(new_ex)

    examples = [Example(x, True) for x in valid_exs]
    examples += [Example(x, False) for x in invalid_exs]

    return examples
