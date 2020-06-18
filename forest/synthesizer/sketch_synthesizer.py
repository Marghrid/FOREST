import itertools
import time
from copy import deepcopy
from datetime import datetime

import z3

from forest.decider import RegexDecider
from forest.dsl import ApplyNode, Node
from forest.dsl.dsl_builder import DSLBuilder
from forest.enumerator import DynamicMultiTreeEnumerator
from forest.logger import get_logger
from forest.synthesizer import MultipleSynthesizer
from forest.utils import transpose
from forest.visitor import RegexInterpreter, ToZ3

logger = get_logger('forest.synthesizer')
m_counter = 0
sketching = ('smt', 'brute-force', 'hybrid')


class SketchSynthesizer(MultipleSynthesizer):
    def __init__(self, valid_examples, invalid_examples, main_dsl, ground_truth,
                 sketching_mode, pruning=False, auto_interaction=False,
                 force_dynamic=False):
        super().__init__(valid_examples, invalid_examples, main_dsl, ground_truth,
                         pruning, auto_interaction)

        self.valid = valid_examples
        self.invalid = invalid_examples
        self.sketching_mode = sketching_mode
        if sketching_mode not in sketching:
            logger.warning(f'Unknown sketching mode: {sketching_mode}. '
                           f'Using \'brute-force\' instead.')
            self.sketching_mode = 'brute-force'
        self.to_z3 = ToZ3()

        self.main_dsl = main_dsl
        self.special_chars = {'.', '^', '$', '*', '+', '?', '\\', '|', '(', ')',
                              '{', '}', '[', ']', '"'}

        self.force_dynamic = force_dynamic

        self.count_level_sketches = 0
        self.count_total_sketches = 0
        self.count_good_sketches = 0
        self.count_sat_calls = 0
        self.count_unsat_calls = 0
        self.time_sat_calls = 0
        self.time_unsat_calls = 0

    def synthesize(self):
        self.start_time = time.time()

        logger.info("Using Dynamic Multi-tree enumerator.")
        self._decider = RegexDecider(interpreter=RegexInterpreter(),
                                     examples=self.examples)
        sizes = list(itertools.product(range(3, 10), range(1, 10)))
        sizes.sort(key=lambda t: (2 ** t[0] - 1) * t[1])
        for dep, length in sizes:
            logger.info(f'Sketching programs of depth {dep} and length {length}...')
            self._enumerator = DynamicMultiTreeEnumerator(self.main_dsl, depth=dep,
                                                          length=length)

            self.try_for_depth()

            print("level sketches", self.count_level_sketches)
            self.count_total_sketches += self.count_level_sketches
            self.count_level_sketches = 0
            print("good sketches", self.count_good_sketches)
            print("\ntotal sketches", self.count_total_sketches)
            if self.count_good_sketches > 0:
                return self.programs[0]
            self.count_good_sketches = 0
            if len(self.programs) > 0:
                return self.programs[0]
            elif self.die:
                return
        return None

    def try_for_depth(self):
        sketch = self.enumerate()
        solve_time = 0
        while sketch is not None and not self.die:
            new_predicates = None
            # logger.debug(f'Sketch: {self._printer.eval(sketch, [0])}.')

            if self.pruning:
                self._enumerator.update(new_predicates)
            else:
                self._enumerator.update(None)

            self.count_level_sketches += 1

            if self.sketching_mode == 'brute-force':
                start0 = time.time()
                filled = self.fill_brute_force(sketch)
                solve_time += time.time() - start0
            else:  # if self.sketching_mode == 'smt':
                start1 = time.time()
                filled = self.fill_smt(sketch)
                solve_time += time.time() - start1

            self.programs.extend(filled)

            if len(filled) > 0:
                self.count_good_sketches += 1
                logger.info(f'Sketch accepted. {self._printer.eval(sketch)}. '
                            f'{len(filled)} concrete programs.')
                for program in filled:
                    logger.info(
                        f'Program accepted. {self._printer.eval(program)}. {self._node_counter.eval(program, [0])} nodes.')
                    # f'{self.num_enumerated} attempts '
                    # f'and {round(time.time() - self.start_time, 2)} seconds:')

            while len(self.programs) > 1:
                self.distinguish()

            sketch = self.enumerate()

        # ----- SMT -------
        print("time (s):", round(solve_time, 2))
        print("total time sat calls (s):", round(self.time_sat_calls, 2))
        print("num sat calls (s):", self.count_sat_calls)
        if self.count_sat_calls > 0:
            print("avg time sat calls (s):",
                  round(self.time_sat_calls / self.count_sat_calls, 2))
        print("total time unsat calls (s):", round(self.time_unsat_calls, 2))
        print("num unsat calls (s):", self.count_unsat_calls)
        if self.count_unsat_calls > 0:
            print("avg time unsat calls (s):",
                  round(self.time_unsat_calls / self.count_unsat_calls, 2))

        if len(self.programs) > 0 or self.die:
            self.terminate()

    def fill_brute_force(self, sketch):
        """ Fills a sketch and returns all resulting concrete valid programs """
        builder = DSLBuilder([0] * len(self.valid[0]), self.valid, self.invalid)
        regexlits = builder.get_regexlits(transpose(self.valid)[0])
        rangelits = builder.get_rangelits(transpose(self.valid)[0])

        # The first traverse is just to save the domain. Ideally 'fill' does not modify
        # the sketch.
        holes = self.traverse_and_save_holes(sketch)

        domains = []
        for hole in holes:
            if hole.type.name == "RegexLit":
                domains.append(regexlits)
            elif hole.type.name == "RangeLit":
                domains.append(rangelits)
            else:
                print("Error:", hole.type.name)

        start = time.time()
        correct = []

        for values in itertools.product(*domains):
            concrete = deepcopy(sketch)
            holes = self.traverse_and_save_holes(concrete)
            assert len(values) == len(holes)
            for i, hole in enumerate(holes):
                hole.data = values[i]

            res = self._decider.analyze(concrete)
            if res.is_ok():
                correct.append(concrete)

        if len(correct) > 0:
            self.count_sat_calls += 1
            self.time_sat_calls += (time.time() - start)
        else:
            self.count_unsat_calls += 1
            self.time_unsat_calls += (time.time() - start)

        return correct

    def _get_new_m(self):
        global m_counter
        m_counter = m_counter + 1
        return f'm_{m_counter - 1}'

    def fill_smt(self, sketch):
        global m_counter
        m_counter = 0
        builder = DSLBuilder([0] * len(self.valid[0]), self.valid, self.invalid)
        regexlits = builder.get_regexlits(transpose(self.valid)[0])
        rangelits = builder.get_rangelits(transpose(self.valid)[0])
        z3_solver = z3.Solver()

        holes = self.traverse_and_save_holes(sketch)
        # print("holes", holes)

        domains = []
        for hole in holes:
            if hole.type.name == "RegexLit":
                domains.append(regexlits)
            elif hole.type.name == "RangeLit":
                domains.append(rangelits)
            else:
                print("Error:", hole.type.name)

        start = time.time()

        m_vars = {}
        for values in itertools.product(*domains):
            concrete = deepcopy(sketch)
            holes = self.traverse_and_save_holes(concrete)
            assert len(values) == len(holes)
            for i, hole in enumerate(holes):
                hole.data = values[i]

            # print("filled", self._printer.eval(program))
            z3re = self.to_z3.eval(concrete)
            m = z3.Bool(self._get_new_m())
            m_vars[m] = concrete

            big_and = []
            for v in self.valid:
                v_s = v[0]
                big_and.append(z3.InRe(v_s, z3re))
            for i in self.invalid:
                i_s = i[0]
                big_and.append(z3.Not(z3.InRe(i_s, z3re)))

            z3_solver.add(m == z3.And(big_and))

        z3_solver.add(z3.Or(*m_vars.keys()))

        res = z3_solver.check()
        if res == z3.sat:
            self.count_sat_calls += 1
            self.time_sat_calls += (time.time() - start)
            # print("s", end=" ")
            # return the list of all programs that are correct, which correspond to the
            # m variables that were assigned true.
            ret_val = list(map(lambda k: m_vars[k],
                               filter(lambda m: z3_solver.model()[m], m_vars.keys())))
            assert len(ret_val) > 0
            return ret_val
        else:
            self.count_unsat_calls += 1
            self.time_unsat_calls += (time.time() - start)
            # print("u", end=" ")
            return []

    def traverse_and_save_holes(self, node: Node):
        if node.is_enum() and node.data == "hole":
            return [node]
        holes = []
        for child in node.children:
            holes.extend(self.traverse_and_save_holes(child))
        return holes
