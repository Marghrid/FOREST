import time
from itertools import combinations
from typing import List

import z3

from forest.distinguisher import Distinguisher
from forest.visitor import Validation_z3, ValidationPrinter


class MultiDistinguisher:
    def __init__(self):
        self._validation2z3 = Validation_z3()
        self.distinguisher = Distinguisher()
        self.printer = ValidationPrinter()

    def distinguish(self, regexes):
        self.fleißig_distinguish(regexes)
        self.lazy_distinguish(regexes)
        exit()

    def fleißig_distinguish(self, regexes: List):
        print("\n===== fleißig =====")
        start = time.time()
        solver = z3.Optimize()

        z3_regexes = []
        for regex in regexes:
            z3_regex = self._validation2z3.eval(regex, ["IN"])
            z3_regexes.append(z3_regex)

        dist = z3.String("distinguishing")
        # solver.add(z3.Length(dist) <= 6)

        ro_z3 = []
        for i, regex in enumerate(z3_regexes):
            ro = z3.Bool(f"ro_{i}")
            ro_z3.append(ro)
            solver.add(ro == z3.InRe(dist, regex))

        # ro_z3[i] == true if dist matches regex[i].

        z3_bs = []
        for i, j in combinations(ro_z3, 2):
            solver.add_soft(z3.Xor(i,j))

        # PbLe([(Bool('b%i' % i), 1) for i in range(200)], 10)

        # print(solver.model)
        res = solver.check()
        print(solver.objectives())
        print("took", round(time.time() - start, 2), "seconds")
        if res == z3.sat:
            print(solver.model())
            return str(solver.model()[dist]).strip('"')
        else:
            print("unsat")
            return None

    def lazy_distinguish(self, regexes: List):
        print("\n===== lazy =====")
        start = time.time()
        dist_inputs = []
        for ri, rj in combinations(regexes, 2):
            dist_input = self.distinguisher.distinguish(ri, rj)
            if dist_input is None:
                print("Programs are indistinguishable")
                longest = max((ri, rj), key=lambda p: len(self.printer.eval(p, ["IN"])))
                regexes.remove(longest)
            else:
                dist_inputs.append(dist_input)
        print(dist_inputs)
        solver = z3.Optimize()
        z3_regexes = []

        for regex in regexes:
            z3_regex = self._validation2z3.eval(regex, ["IN"])
            z3_regexes.append(z3_regex)

        dist = z3.String("distinguishing")
        big_or = []
        for dist_input in dist_inputs:
            big_or.append(dist == z3.StringVal(dist_input))

        solver.add(z3.Or(big_or))

        ro_z3 = []

        for i, regex in enumerate(z3_regexes):
            ro = z3.Bool(f"ro_{i}")
            ro_z3.append(ro)
            solver.add(ro == z3.InRe(dist, regex))

        z3_bs = []
        for i, j in combinations(ro_z3, 2):
            solver.add_soft(z3.Xor(i,j))

        # print(solver.model)
        res = solver.check()
        print(solver.objectives())
        print("took", round(time.time() - start, 2), "seconds")
        if res == z3.sat:
            print(solver.model())
            return str(solver.model()[dist]).strip('"')
        else:
            print("unsat")
            return None
