from tyrell.decider import Example


def parse_file(filename):
	valid_exs = []
	invalid_exs = []
	with open(filename, "r") as in_file:
		next_line = in_file.readline()
		while next_line and not next_line.startswith("++"):
			next_line = in_file.readline()

		next_line = in_file.readline() # skip line with "++"
		while next_line and not next_line.startswith("--"):
			next_line = next_line.rstrip()
			if len(next_line) > 0:
				valid_exs.append([i.strip() for i in next_line.split(',')])
			next_line = in_file.readline()

		next_line = in_file.readline() # skip line with "--"
		while next_line:
			next_line = next_line.rstrip()
			if len(next_line) > 0:
				invalid_exs.append([i.strip() for i in next_line.split(',')])
			next_line = in_file.readline()

	print(valid_exs)

	examples = [Example(x, True) for x in valid_exs]
	examples += [Example(x, False) for x in invalid_exs]

	return examples


