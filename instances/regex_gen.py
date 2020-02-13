import random
import string

for i in range(20):
	new = ''.join(random.choices(string.digits, k=1))
	new += '-'
	new += ''.join(random.choices(string.ascii_uppercase, k=1))
	new += ''.join(random.choices(string.ascii_uppercase, k=1))
	print(new)