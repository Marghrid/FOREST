import itertools
import re
import time
from copy import deepcopy

import z3

from forest.decider import RegexDecider
from forest.dsl import Node
from forest.dsl.dsl_builder import DSLBuilder
from forest.enumerator import DynamicMultiTreeEnumerator, StaticMultiTreeEnumerator
from forest.logger import get_logger
from forest.synthesizer import MultipleSynthesizer
from forest.utils import transpose, find_all_cs
from forest.visitor import RegexInterpreter, ToZ3

logger = get_logger('forest')
m_counter = 0
sketching = ('smt', 'brute-force', 'hybrid')


class SketchSynthesizer(MultipleSynthesizer):
    def __init__(self, valid_examples, invalid_examples, captured, condition_invalid,
                 main_dsl, ground_truth, sketching_mode, pruning=False,
                 auto_interaction=False, force_dynamic=False):
        super().__init__(valid_examples, invalid_examples, captured, condition_invalid,
                         main_dsl, ground_truth, pruning, auto_interaction)

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
        self.time_sat_encoding = 0
        self.time_unsat_calls = 0
        self.time_unsat_encoding = 0
        self.count_smt_unknown_sat = 0
        self.count_smt_unknown_unsat = 0
        self.warned = False

    def synthesize(self):
        self.start_time = time.time()

        self.start_time = time.time()
        try:
            valid, invalid = self.split_examples()
        except:
            valid = None
            invalid = None

        if valid is not None and len(valid[0]) > 1 and not self.force_dynamic:
            # self.valid = valid
            # self.invalid = invalid

            assert all(map(lambda l: len(l) == len(valid[0]), valid))
            assert all(map(lambda l: len(l) == len(invalid[0]), invalid))

            type_validations = ['is_regex'] * len(valid[0])
            builder = DSLBuilder(type_validations, valid, invalid, sketches=True)
            dsls = builder.build()

            logger.info("Using Static Multi-tree enumerator.")
            self._decider = RegexDecider(interpreter=RegexInterpreter(),
                                         examples=self.examples,
                                         split_valid=valid)
            for depth in range(2, 10):
                self._enumerator = StaticMultiTreeEnumerator(self.main_dsl, dsls, depth)

                self.try_for_depth()

                print("level sketches", self.count_level_sketches)
                self.count_total_sketches += self.count_level_sketches
                self.count_level_sketches = 0
                print("good sketches", self.count_good_sketches)
                print("\ntotal sketches", self.count_total_sketches)
                if self.count_good_sketches > 0:
                    return self.solutions[0]
                self.count_good_sketches = 0
                if len(self.solutions) > 0:
                    return self.solutions[0]
                elif self.die:
                    return

        else:
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
                    return self.solutions[0]
                self.count_good_sketches = 0
                if len(self.solutions) > 0:
                    return self.solutions[0]
                elif self.die:
                    return

    def try_for_depth(self):
        sketch = self.enumerate()
        solve_time = 0
        while sketch is not None and not self.die:
            logger.debug(f'Sketch: {self._printer.eval(sketch, [0])}.')

            self._enumerator.update(None)
            self.count_level_sketches += 1

            if self.sketching_mode == 'brute-force':
                start0 = time.time()
                filled = self.fill_brute_force(sketch)
                solve_time += time.time() - start0
            elif self.sketching_mode == 'smt':
                start1 = time.time()
                filled = self.fill_smt(sketch)
                solve_time += time.time() - start1
            elif self.sketching_mode == 'hybrid':
                start2 = time.time()
                filled = self.fill_hybrid(sketch)
                solve_time += time.time() - start2
            else:
                logger.error("Unknown sketching method:", self.sketching_mode)
                return

            self.solutions.extend(filled)

            if len(filled) > 0:
                self.count_good_sketches += 1
                logger.info(f'Sketch accepted. {self._printer.eval(sketch)}. '
                            f'{len(filled)} concrete programs.')
                for program in filled:
                    logger.info(
                        f'Program accepted. {self._printer.eval(program)}. {self._node_counter.eval(program, [0])} nodes.')
                    # f'{self.num_enumerated} attempts '
                    # f'and {round(time.time() - self.start_time, 2)} seconds:')

            while len(self.solutions) > 1:
                self.distinguish()

            sketch = self.enumerate()

        # ----- SMT -------
        print("time (s):", round(solve_time, 2))
        print("total time sat calls (s):", round(self.time_sat_calls, 2))
        print("total time sat encoding (s):", round(self.time_sat_encoding, 2))
        print("num sat calls (s):", self.count_sat_calls)
        if self.count_sat_calls > 0:
            print("avg time sat calls (s):",
                  round(self.time_sat_calls / self.count_sat_calls, 2))
            print("avg time sat encoding (s):",
                  round(self.time_sat_encoding / self.count_sat_calls, 2))
        print("total time unsat calls (s):", round(self.time_unsat_calls, 2))
        print("total time unsat encoding (s):", round(self.time_unsat_encoding, 2))
        print("num unsat calls (s):", self.count_unsat_calls)
        if self.count_unsat_calls > 0:
            print("avg time unsat calls (s):",
                  round(self.time_unsat_calls / self.count_unsat_calls, 2))
            print("avg time unsat encoding (s):",
                  round(self.time_unsat_encoding / self.count_unsat_calls, 2))

        print("num unk-sat calls (s):", self.count_smt_unknown_sat)
        print("num unk-unsat calls (s):", self.count_smt_unknown_unsat)

        if len(self.solutions) > 0 or self.die:
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

    def fill_hybrid(self, sketch):
        global m_counter
        m_counter = 0
        builder = DSLBuilder([0] * len(self.valid[0]), self.valid, self.invalid)
        regexlits = builder.get_regexlits(transpose(self.valid)[0])
        rangelits = builder.get_rangelits(transpose(self.valid)[0])
        z3_solver = z3.Solver()
        try:
            z3_solver.set('smt.seq.use_derivatives', True)
            z3_solver.check()
        except:
            if not self.warned:
                logger.warning("'use_derivatives' option not available.")
                self.warned = True

        holes = self.traverse_and_save_holes(sketch)
        # print("holes", holes)

        print("Generating domains...")
        domains = []
        for hole in holes:
            if hole.type.name == "RegexLit":
                domains.append(regexlits)
            elif hole.type.name == "RangeLit":
                domains.append(rangelits)
            else:
                print("Error:", hole.type.name)

        start = time.time()

        print("Creating constraints...", len(list(itertools.product(*domains))))
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
        builder = DSLBuilder([0] * len(self.valid[0]), self.valid, self.invalid)
        regexlits = builder.get_regexlits(transpose(self.valid)[0])
        rangelits = builder.get_rangelits(transpose(self.valid)[0])
        z3_solver = z3.Solver()
        try:
            z3_solver.set('smt.seq.use_derivatives', True)
            z3_solver.check()
        except:
            if not self.warned:
                logger.warning("'use_derivatives' option not available.")
                self.warned = True

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

        m_vars = {}
        for values in itertools.product(*domains):
            concrete = deepcopy(sketch)
            holes = self.traverse_and_save_holes(concrete)
            assert len(values) == len(holes)
            for i, hole in enumerate(holes):
                hole.data = values[i]

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

    def split_examples(self):
        max_l = max(map(lambda x: len(x[0]), self.valid))
        new_l = len(self.valid[0])
        l = 0
        valid = deepcopy(self.valid)
        invalid = deepcopy(self.invalid)
        while new_l != l and l < max_l:
            l = new_l
            transposed_valid = transpose(valid)

            for field_idx, field in enumerate(transposed_valid):
                common_substrings = find_all_cs(field)
                if len(common_substrings) == 1:
                    rec = re.compile(self.build_regex(common_substrings[0]))
                    if all(map(lambda f: rec.fullmatch(f) is not None, field)):
                        continue
                    if all(map(lambda f: len(f) == len(common_substrings[0]), field)):
                        continue
                for cs in common_substrings:
                    rec = re.compile(self.build_regex(cs))
                    matches = list(map(lambda ex: rec.findall(ex), field))
                    if all(map(lambda m: len(m) == len(matches[0]), matches)):
                        valid, invalid = self.split_examples_on(valid, invalid, cs,
                                                                field_idx)

            new_l = len(valid[0])

        valid, invalid = self.remove_empties(valid, invalid)

        if not all(map(lambda l: len(l) == len(valid[0]), valid)):
            return None, None
        if len(invalid) > 0 and \
                not all(map(lambda l: len(l) == len(valid[0]), invalid)):
            return None, None

        return valid, invalid

    def split_examples_on(self, valid, invalid, substring: str, field_idx: int):
        rec = re.compile(self.build_regex(substring))
        for ex_idx, example in enumerate(valid):
            field = example[field_idx]
            split = rec.split(field, 1)
            example = example[:field_idx] + split + example[field_idx + 1:]
            valid[ex_idx] = example
            pass

        remaining_invalid = []
        for ex_idx, example in enumerate(invalid):
            field = example[field_idx]
            split = rec.split(field, 1)
            example = example[:field_idx] + split + example[field_idx + 1:]
            if len(example) == len(valid[0]):
                remaining_invalid.append(example)
        invalid = remaining_invalid

        return valid, invalid

    def build_regex(self, cs):
        if isinstance(cs, str):
            if cs in self.special_chars:
                return f'(\\{cs}+)'
            elif len(cs) == 1:
                return fr'({cs}+)'
            else:
                ret = ''
                ret = '((?:'
                for char in cs:
                    if char in self.special_chars:
                        ret += "\\"
                    ret += char
                ret += ")+)"
                return ret  # fr'((?:{cs})+)'
        elif isinstance(cs, list):
            pass

    def remove_empties(self, valid, invalid):
        for field_idx, field in enumerate(valid[0]):
            if len(field) == 0 and all(
                    map(lambda ex: len(ex[field_idx]) == 0, valid)):
                # ensure this field is the empty string on all examples
                invalid = list(
                    filter(lambda ex: len(ex[field_idx]) == 0, invalid))
                for ex in valid + invalid:
                    ex.pop(field_idx)
        return valid, invalid
