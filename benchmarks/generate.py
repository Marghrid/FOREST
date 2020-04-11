import random
import string

'[A-Z]{4}[0-9]{6}[A-Z]{6}[0-9]{2}'

def num():
	return random.choice(string.digits)
def let():
	return random.choice(string.ascii_uppercase)

for i in range(10):
	l0 = let() + let() + let() + let()
	l1 = num() + num() + num() + num() + num() + num()
	l2 = let() + let() + let() + let() + let() + let()
	l3 = num() + num()

	print(l0+l1+l2+l3)