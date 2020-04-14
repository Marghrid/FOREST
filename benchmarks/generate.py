import random
import string

def num():
	return random.choice(string.digits)
def cap():
	return random.choice(string.ascii_uppercase)
def let():
	return random.choice(string.ascii_uppercase)

def capnum():
	return random.choice(string.digits + string.ascii_uppercase + string.digits)
def hexa():
	return random.choice(string.digits + 'ABCDEF')

for i in range(15):
	l1 = hexa() + hexa() + hexa() + hexa()
	l2 = hexa() + hexa() + hexa() + hexa()
	l3 = hexa() + hexa() + hexa() + hexa()
	l4 = hexa() + hexa() + hexa() + hexa()
	l5 = hexa() + hexa() + hexa() + hexa()
	l6 = hexa() + hexa() + hexa() + hexa()
	l7 = hexa() + hexa() + hexa() + hexa()
	l8 = hexa() + hexa() + hexa() + hexa()

	print(l1+':'+l2+':'+l3+':'+l4+':'+l5+':'+l6+':'+l7+':'+l8)