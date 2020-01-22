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
				valid_exs.append(next_line)
			next_line = in_file.readline()

		next_line = in_file.readline() # skip line with "--"
		while next_line:
			next_line = next_line.rstrip()
			if len(next_line) > 0:
				invalid_exs.append(next_line)
			next_line = in_file.readline()

	return (valid_exs, invalid_exs)

print(parse_file("instances/age2.txt"))

