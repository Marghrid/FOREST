import itertools
import time
from copy import deepcopy

import z3

from forest.configuration import Configuration
from forest.decider import RegexDecider
from forest.dsl import Node
from forest.dsl.dsl_builder import DSLBuilder
from forest.enumerator import DynamicMultiTreeEnumerator, StaticMultiTreeEnumerator
from forest.logger import get_logger
from forest.stats import Statistics
from forest.synthesizer import MultiTreeSynthesizer
from forest.utils import transpose
from forest.visitor import RegexInterpreter, ToZ3

logger = get_logger('forest')
stats = Statistics.get_statistics()
m_counter = 0
sketching = ('smt', 'brute-force', 'hybrid')


def _get_new_m():
    global m_counter
    m_counter = m_counter + 1
    return f'm_{m_counter - 1}'


class SketchSynthesizer(MultiTreeSynthesizer):
    def __init__(self, valid_examples, invalid_examples, captured, condition_invalid,
                 main_dsl, ground_truth, configuration: Configuration):
        super().__init__(valid_examples, invalid_examples, captured, condition_invalid,
                         main_dsl, ground_truth, configuration=configuration)

        if configuration.sketching not in sketching:
            logger.warning(f'Unknown sketching mode: {configuration.sketching}. '
                           f'Using \'brute-force\' instead.')
            self.configuration.sketching = 'brute-force'

        self.to_z3 = ToZ3()

        self.main_dsl = main_dsl
        self.special_chars = {'.', '^', '$', '*', '+', '?', '\\', '|', '(', ')',
                              '{', '}', '[', ']', '"'}

        self.count_level_sketches = 0
        self.count_total_sketches = 0
        self.count_good_sketches = 0
        self.count_sat_calls = 0
        self.count_unsat_calls = 0
        self.time_sat_calls = 0
        self.time_sat_encoding = 0
        self.time_unsat_calls = 0
        self.time_unsat_encoding = 0
        self.count_smt_unknown_sat = 0
        self.count_smt_unknown_unsat = 0

    def synthesize(self):
        self.start_time = time.time()
        try:
            valid, invalid = self.split_examples()
        except:
            valid = None
            invalid = None

        if valid is not None and len(valid[0]) > 1 and not self.configuration.force_dynamic:
            # self.valid = valid
            # self.invalid = invalid
            self._decider = RegexDecider(RegexInterpreter(), valid, invalid, split_valid=valid)

            assert all(map(lambda l: len(l) == len(valid[0]), valid))
            assert all(map(lambda l: len(l) == len(invalid[0]), invalid))

            type_validations = ['regex'] * len(valid[0])
            builder = DSLBuilder(type_validations, valid, invalid, sketches=True)
            dsls = builder.build()

            for depth in range(2, 10):
                self._enumerator = StaticMultiTreeEnumerator(self.main_dsl, dsls, depth)

                depth_start = time.time()
                self.try_for_depth()
                stats.per_depth_times[depth] = time.time() - depth_start

                print("level sketches", self.count_level_sketches)
                self.count_total_sketches += self.count_level_sketches
                self.count_level_sketches = 0
                print("good sketches", self.count_good_sketches)
                print("\ntotal sketches", self.count_total_sketches)

                if self.count_good_sketches > 0:
                    self.terminate()
                    return self.solutions[0]
                self.count_good_sketches = 0

                if len(self.solutions) > 0:
                    self.terminate()
                    return self.solutions[0]
                elif self.configuration.die:
                    self.terminate()
                    return

        else:
            self._decider = RegexDecider(RegexInterpreter(), valid, invalid)
            sizes = list(itertools.product(range(3, 10), range(1, 10)))
            sizes.sort(key=lambda t: (2 ** t[0] - 1) * t[1])
            for dep, length in sizes:
                logger.info(f'Sketching programs of depth {dep} and length {length}...')
                self._enumerator = DynamicMultiTreeEnumerator(self.main_dsl, depth=dep, length=length)

                depth_start = time.time()
                self.try_for_depth()
                stats.per_depth_times[(dep, length)] = time.time() - depth_start

                print("level sketches", self.count_level_sketches)
                self.count_total_sketches += self.count_level_sketches
                self.count_level_sketches = 0
                print("good sketches", self.count_good_sketches)
                print("\ntotal sketches", self.count_total_sketches)

                if self.count_good_sketches > 0:
                    self.terminate()
                    return self.solutions[0]
                self.count_good_sketches = 0

                if len(self.solutions) > 0:
                    self.terminate()
                    return self.solutions[0]
                elif self.configuration.die:
                    self.terminate()
                    return

    def try_regex(self):
        """ Tries to synthesize a regex that matches the valid and invalid examples using the
        current sketch. """
        regex_synthesis_start = time.time()

        sketch = self.enumerate()
        if sketch is None:
            return None

        logger.info(f'Sketch: {self._printer.eval(sketch, [0])}')

        if self.configuration.sketching == 'brute-force':
            filled = self.fill_brute_force(sketch)
        elif self.configuration.sketching == 'smt':
            filled = self.fill_smt(sketch)
        elif self.configuration.sketching == 'hybrid':
            filled = self.fill_hybrid(sketch)
        else:
            logger.error("Unknown sketching method:", self.configuration.sketching)
            return

        self._enumerator.update()
        stats.regex_synthesis_time += time.time() - regex_synthesis_start
        self.count_level_sketches += 1

        if len(filled) > 0:
            self.count_good_sketches += 1
            logger.info(f'Sketch accepted. {self._printer.eval(sketch)}. '
                        f'{len(filled)} concrete programs.')
            for program in filled:
                logger.info(
                    f'Program accepted. {self._printer.eval(program)}. '
                    f'{self._node_counter.eval(program, [0])} nodes.')
                # f'{self.num_enumerated} attempts '
                # f'and {round(time.time() - self.start_time, 2)} seconds:')

            if stats.first_regex_time == -1:
                stats.first_regex_time = time.time() - self.start_time
                self.first_regex = filled[0]

            return filled[0]

        return -1

    def get_domains(self, sketch):
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
        return domains

    def fill_brute_force(self, sketch):
        """ Fills a sketch and returns all resulting concrete valid programs """
        domains = self.get_domains(sketch)

        start = time.time()
        correct = []

        for values in itertools.product(*domains):
            if self.configuration.die:
                break
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

    def fill_hybrid(self, sketch):
        domains = self.get_domains(sketch)

        z3_solver = z3.Solver()
        try:
            z3_solver.set('smt.seq.use_derivatives', True)
            z3_solver.check()
        except:
            pass

        start = time.time()

        m_vars = {}
        for values in itertools.product(*domains):
            if self.configuration.die:
                break
            concrete = deepcopy(sketch)
            holes = self.traverse_and_save_holes(concrete)
            assert len(values) == len(holes)
            for i, hole in enumerate(holes):
                hole.data = values[i]

            z3re = self.to_z3.eval(concrete)
            m = z3.Bool(_get_new_m())
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

        z3_solver.set("timeout", 100)
        print("checking...")
        res = z3_solver.check()
        print("done.")

        if res == z3.sat:
            self.count_sat_calls += 1
            self.time_sat_calls += (time.time() - start)
            ret_val = list(map(lambda k: m_vars[k],
                               filter(lambda m: z3_solver.model()[m], m_vars.keys())))
            assert len(ret_val) > 0
            return ret_val
        elif res == z3.unsat:
            self.count_unsat_calls += 1
            self.time_unsat_calls += (time.time() - start)
            return []
        elif res == z3.unknown:
            print("SMT unknown.")
            stop_time = time.time()
            correct = self.fill_brute_force(sketch)
            if len(correct) > 0:
                self.time_sat_calls += (stop_time - start)
                self.count_smt_unknown_sat += 1
            else:
                self.time_unsat_calls += (stop_time - start)
                self.count_smt_unknown_unsat += 1

            return correct
        else:
            logger.error("Unknown Z3 response", res)

    def fill_smt(self, sketch):
        global m_counter
        m_counter = 0

        domains = self.get_domains(sketch)

        z3_solver = z3.Solver()
        try:
            z3_solver.set('smt.seq.use_derivatives', True)
            z3_solver.check()
        except:
            pass

        start = time.time()

        m_vars = {}
        for values in itertools.product(*domains):
            if self.configuration.die:
                break
            concrete = deepcopy(sketch)
            holes = self.traverse_and_save_holes(concrete)
            assert len(values) == len(holes)
            for i, hole in enumerate(holes):
                hole.data = values[i]

            z3re = self.to_z3.eval(concrete)
            m = z3.Bool(_get_new_m())
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

        time_encoding = (time.time() - start)

        start = time.time()
        res = z3_solver.check()
        if res == z3.sat:
            self.count_sat_calls += 1
            self.time_sat_calls += (time.time() - start)
            self.time_sat_encoding += time_encoding
            ret_val = list(map(lambda k: m_vars[k],
                               filter(lambda m: z3_solver.model()[m], m_vars.keys())))
            assert len(ret_val) > 0
            return ret_val
        else:
            self.count_unsat_calls += 1
            self.time_unsat_calls += (time.time() - start)
            self.time_unsat_encoding += time_encoding
            return []

    def traverse_and_save_holes(self, node: Node):
        if node.is_enum() and node.data == "hole":
            return [node]
        holes = []
        for child in node.children:
            holes.extend(self.traverse_and_save_holes(child))
        return holes
