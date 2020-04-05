import glob

from tyrell.common_substrings import find_all_cs
from tyrell.parse_examples import parse_file

instance_paths = []

dir = 'instances/strings/'
instance_paths += glob.glob(dir + "*.txt")

dir = 'instances/strings/ambiguous/'
instance_paths += glob.glob(dir + "*.txt")

dir = 'instances/strings/hard/'
instance_paths += glob.glob(dir + "*.txt")

for examples_file in instance_paths:
    print('\n', examples_file)
    valid, invalid = parse_file(examples_file)
    transposed_valid = list(map(list, zip(*valid)))
    print(transposed_valid)
    substrings = []
    for field in transposed_valid:

        substrings.extend(find_all_cs(field))

    print(substrings)