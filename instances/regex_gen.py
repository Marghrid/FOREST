import random
import string

for i in range(20):
	string_set = random.choice([string.digits, string.ascii_uppercase])
	new = ''.join(random.choices(string_set, k=2))
	new += '-'
	string_set = random.choice([string.digits, string.ascii_uppercase])
	new += ''.join(random.choices(string_set, k=2))
	new += '-'
	string_set = random.choice([string.digits, string.ascii_uppercase])
	new += ''.join(random.choices(string_set, k=2))
	print(new)