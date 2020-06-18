import z3

from forest.visitor import ToZ3


class Distinguisher:
    def __init__(self):
        self._validation2z3 = ToZ3()

    def distinguish(self, r1, r2):
        """ Returns a distinguishing input for regexes r1 and r2, or None if they are
        equivalent """
        solver = z3.Solver()
        solver.set('random_seed', 7)
        solver.set('sat.random_seed', 7)

        z3_r1 = self._validation2z3.eval(r1, ["IN"])
        z3_r2 = self._validation2z3.eval(r2, ["IN"])

        dist = z3.String("distinguishing")
        dist_in_r1 = z3.InRe(dist, z3_r1)
        dist_in_r2 = z3.InRe(dist, z3_r2)

        solver.add(dist_in_r1 != dist_in_r2)
        res = solver.check()

        if res == z3.sat:
            return str(solver.model()[dist]).strip('"')
        else:
            return None
