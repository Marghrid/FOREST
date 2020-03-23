import z3

from tyrell.interpreter import Validation_z3


class Distinguisher:
    def __init__(self):
        self._validation2z3 = Validation_z3()

    def distinguish(self, prog1, prog2):
        solver = z3.Solver()
        solver.set('random_seed', 0)
        solver.set('sat.random_seed', 0)
        z3_prog1 = self._validation2z3.eval(prog1, ["IN"])
        z3_prog2 = self._validation2z3.eval(prog2, ["IN"])

        dist = z3.String("distinguishing")

        dist_in_p1 = z3.InRe(dist, z3_prog1)
        dist_in_p2 = z3.InRe(dist, z3_prog2)

        solver.add(dist_in_p1 != dist_in_p2)

        res = solver.check()
        if res == z3.sat:
            return str(solver.model()[dist]).strip('"')
        else: return None
