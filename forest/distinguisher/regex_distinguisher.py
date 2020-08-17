import random
import time
from itertools import combinations

import z3

from forest.logger import get_logger
from forest.visitor import ToZ3, RegexInterpreter

logger = get_logger('forest')

use_derivatives = True


class RegexDistinguisher:
    def __init__(self):
        self._toz3 = ToZ3()
        self._printer = RegexInterpreter()
        self.force_multi_distinguish = False
        self.force_distinguish2 = False

    def distinguish(self, programs):
        logger.debug(f"Distinguishing {len(programs)}: "
                     f"{','.join(map(self._printer.eval, programs))}")
        assert len(programs) >= 2
        if not self.force_multi_distinguish and len(programs) == 2:
            return self.distinguish2(programs[0], programs[1])
        if self.force_distinguish2:
            dist_input, keep_if_valid, keep_if_invalid, _ = \
                self.distinguish2(programs[0], programs[1])
            return dist_input, keep_if_valid, keep_if_invalid, programs[2:]
        else:
            return self.multi_distinguish(programs)

    def distinguish2(self, r1, r2):
        global use_derivatives
        solver = z3.Solver()
        solver.set('random_seed', 7)
        solver.set('sat.random_seed', 7)
        if use_derivatives:
            try:
                solver.set('smt.seq.use_derivatives', True)
                solver.check()
            except:
                logger.warning("'use_derivatives' option not available.")
                use_derivatives = False  # prevents additional calls to check

        z3_r1 = self._toz3.eval(r1)
        z3_r2 = self._toz3.eval(r2)

        dist = z3.String("distinguishing")

        ro_1 = z3.Bool(f"ro_1")
        solver.add(ro_1 == z3.InRe(dist, z3_r1))
        ro_2 = z3.Bool(f"ro_2")
        solver.add(ro_2 == z3.InRe(dist, z3_r2))

        solver.add(ro_1 != ro_2)

        if solver.check() == z3.sat:
            if solver.model()[ro_1]:
                return str(solver.model()[dist]).strip('"'), [r1], [r2], []
            else:
                return str(solver.model()[dist]).strip('"'), [r2], [r1], []
        else:
            return None, None, None, None

    def multi_distinguish(self, regexes):
        start = time.time()
        # Problem: cannot distinguish more than 4 regexes at once: it takes forever.
        # Solution: use only 4 randomly selected regexes for the SMT maximization,
        # and then add the others to the solution.
        if len(regexes) <= 4:
            selected_regexes = regexes
            others = []
        else:
            random.seed('regex')
            random.shuffle(regexes)
            selected_regexes = regexes[:4]
            others = regexes[4:]
        solver = z3.Optimize()

        z3_regexes = []
        for z3_regex in selected_regexes:
            z3_regex = self._toz3.eval(z3_regex)
            z3_regexes.append(z3_regex)

        dist = z3.String("distinguishing")
        # solver.add(z3.Length(dist) <= 6)

        ro_z3 = []
        for i, z3_regex in enumerate(z3_regexes):
            ro = z3.Bool(f"ro_{i}")
            ro_z3.append(ro)
            solver.add(ro == z3.InRe(dist, z3_regex))

        # ro_z3[i] == true if dist matches regex[i].

        z3_bs = []
        for ro_i, ro_j in combinations(ro_z3, 2):
            solver.add_soft(z3.Xor(ro_i, ro_j))

        # PbLe([(Bool('b%i' % i), 1) for i in range(200)], 10)

        if solver.check() == z3.sat:
            # print(solver.model())
            print("took", round(time.time() - start, 2), "seconds")
            keep_if_valid = []
            keep_if_invalid = []
            dist_input = str(solver.model()[dist]).strip('"')
            for i, ro in enumerate(ro_z3):
                if solver.model()[ro]:
                    keep_if_valid.append(selected_regexes[i])
                else:
                    keep_if_invalid.append(selected_regexes[i])
            if len(keep_if_valid) == 0 or len(keep_if_invalid) == 0:
                if len(others) == 0:
                    return None, None, None, None
                else:  # selected_regexes are equivalent, but the regexes in others may
                    # not be.
                    smallest_regex = min(selected_regexes,
                                         key=lambda r: len(self._printer.eval(r)))
                    others.append(smallest_regex)
                    return self.multi_distinguish(others)
            return dist_input, keep_if_valid, keep_if_invalid, others
        else:
            print("unsat")
            return None, None, None, None