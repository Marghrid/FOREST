import z3

'''
[info] Solution found: is_string(IN) /\ match([A-Z0-9]-[A-Z][0-9], IN)
[info] depth: 5
[info] Solution found: is_string(IN) /\ match([0-9]-[A-Z][0-9], IN)
[info] depth: 5
'''

print("p1: [A-Z0-9]-[A-Z][0-9]")
print("p2: [0-9]-[A-Z][0-9]")

solver = z3.Solver()
rangeAZ = z3.Range('A', 'Z')
range09 = z3.Range('0', '9')
rangeAZ09 = z3.Union(rangeAZ, range09)
minus = z3.Re("-")


p1 = z3.Concat(rangeAZ09, minus, rangeAZ, range09)
p2 = z3.Concat(range09, minus, rangeAZ, range09)

dist = z3.String("distinguishing")


distInP1 = z3.InRe(dist, p1)
distInP2 = z3.InRe(dist, p2)

solver.add(distInP1 != distInP2)

res = solver.check()
if res == z3.sat:
    print(solver.model())

# I want to find x such that InRe(x, p1) != InRe(x, p2)