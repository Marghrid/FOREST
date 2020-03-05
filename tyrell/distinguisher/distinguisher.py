import z3
from tyrell.interpreter import Validation2Z3

class Distinguisher:
    def __init__(self):
        self._validation2z3 = Validation2Z3()

    def distinguish(self, prog1, prog2):
        solver = z3.Solver()
        z3_prog1 = self._validation2z3.eval(prog1, ["IN"])
        z3_prog2 = self._validation2z3.eval(prog2, ["IN"])

        dist = z3.String("distinguishing")

        distInP1 = z3.InRe(dist, z3_prog1)
        distInP2 = z3.InRe(dist, z3_prog2)

        # print("p1", z3_prog1)
        # print("p2", z3_prog2)

        solver.add(distInP1 != distInP2)

        res = solver.check()
        if res == z3.sat:
            return str(solver.model()[dist]).strip('"')
        else: return None
