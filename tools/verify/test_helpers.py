"""Regression tests for the proofs' helpers: the normalizer's proof
context (canon.py), the induction's generalization (induction.py), and the
timing proof's leak detector (aarch64.py).

    python3 -m unittest discover -s tools/verify -p test_helpers.py
"""

import unittest
from z3 import BitVec, BitVecs, Concat, Extract
import canon
import induction


class ContextTests(unittest.TestCase):
    def tearDown(self):
        canon.set_context([], set())

    def test_array_fingerprint_distinguishes_chunk_offsets(self):
        from z3 import Array, BitVecSort, BitVecVal, Select, simplify
        name = "stride_test_input"
        array = Array(name, BitVecSort(64), BitVecSort(8))
        canon._values[(name, 0, 0)] = 0x0123456789ABCDEF
        canon._values[(name, 0, 1)] = 0
        sampled = canon.sample(name, array, 0)
        self.assertEqual(simplify(Select(sampled, BitVecVal(0, 64))).as_long(), 0)
        self.assertEqual(simplify(Select(sampled, BitVecVal(256, 64))).as_long(), 0x23)

    def test_iteration_counter_is_a_parameter(self):
        counter, iteration = BitVecs("counter len_k", 64)
        canon.set_context([], {"len_k"})
        whole = Extract(31, 0, counter + 16 * iteration)
        halves = Extract(31, 0, counter) + 16 * Extract(31, 0, iteration)
        self.assertEqual(canon.canon(whole), canon.canon(halves))
        self.assertNotEqual(canon.canon(whole), canon.canon(halves + 1))

    def test_length_parts_of_a_sum_combine(self):
        # A word plus a group number the kernel computes from an address,
        # against the same word plus K + 1: one normal form; K + 2 differs.
        from z3 import BitVec, LShR, ULE
        word, k = BitVec("pair0", 32), BitVec("len_k", 64)
        canon.set_context([ULE(k, 1 << 39)], {"len_k"})
        computed = word + Extract(31, 0, LShR(1024 * k + 1024 + 5, 10))
        self.assertEqual(canon.canon(computed), canon.canon(word + Extract(31, 0, k) + 1))
        self.assertNotEqual(canon.canon(computed), canon.canon(word + Extract(31, 0, k) + 2))

    def test_context_resets_symbol_classification(self):
        _, iteration = BitVecs("counter len_k", 64)
        self.assertTrue(canon.has_data(iteration))
        canon.set_context([], {"len_k"})
        self.assertFalse(canon.has_data(iteration))
        canon.set_context([], set())
        self.assertTrue(canon.has_data(iteration))


class GeneralizationTests(unittest.TestCase):
    def test_backedge_requires_successor_domain_and_no_wrap(self):
        from types import SimpleNamespace
        from unittest.mock import patch
        from z3 import ULT, UGE
        from aarch64 import Unproved
        k, groups = BitVecs("len_k len_groups", 64)
        state = SimpleNamespace(x={}, v={}, regions={}, lengths={"len_k", "len_groups"}, assumptions=[])
        g = induction.Generalized(state, state, k)
        for assumptions in ([UGE(groups, 1), ULT(k, groups)], []):
            with self.subTest(assumptions=assumptions):
                with patch.object(induction, "paths", side_effect=lambda m, *_: [(m, "head")]):
                    with self.assertRaisesRegex(Unproved, "domain or wraps"):
                        induction.loop_step(g, state, k, assumptions, 0, lambda *_: None)

    def test_iteration_rank_is_a_symbolic_variable(self):
        with self.assertRaisesRegex(AssertionError, "symbolic 64-bit"):
            induction.loop_step(None, None, BitVec("len_k", 64) + 1, [], 0, None)

    def test_constant_difference_through_byte_shuffles(self):
        # A word loaded byte by byte: its bytes' Concat hides the difference
        # from Z3's simplifier.
        x = BitVec("pair0", 32)
        def loaded(t):
            return Concat(Extract(31, 24, t), Extract(23, 16, t), Extract(15, 8, t), Extract(7, 0, t))
        self.assertEqual(induction.constant_difference(loaded(x), loaded(x + 1)), 1)
        self.assertIsNone(induction.constant_difference(x, x * x))

    def test_explicit_counter_halves_at_the_next_iteration(self):
        from types import SimpleNamespace
        from z3 import BitVecVal, simplify, substitute
        state = SimpleNamespace(x={}, v={}, regions={})
        counter, k = BitVecs("counter len_k", 64)
        g = induction.Generalized(state, state, k)
        values = [counter + 8 * k + lane for lane in range(2)]
        inst = g.at(BitVecVal(1, 64))
        # The low word carries while each packed 32-bit lane advances
        # independently. An affine 64-bit packed-word step gets this wrong.
        for high, expected in [(False, 1 << 32), (True, (1 << 32) + 1)]:
            lo = 32 if high else 0
            packed = Concat(Extract(lo + 31, lo, values[1]), Extract(lo + 31, lo, values[0]))
            got = simplify(substitute(inst(packed), (counter, BitVecVal((1 << 32) - 8, 64))))
            self.assertEqual(got.as_long(), expected)


if __name__ == "__main__":
    unittest.main()


class LeakTests(unittest.TestCase):
    """The timing proof's detector: a run stops where the message steers
    a branch or an address, and runs on where only lengths do."""

    def run_code(self, code):
        import aarch64
        from aarch64 import Machine, Region, Ptr
        msg = [BitVec(f"msg{i}", 8) for i in range(16)]
        m = Machine(code, {"input": Region("input", 16, False, lambda o: msg[o]),
                           "table": Region("table", 256, False, lambda o: BitVec(f"t{o}", 8))})
        m.x = {i: BitVec(f"x{i}_in", 64) for i in range(31)}
        m.x[0], m.x[1], m.x[30] = Ptr("input", 0), Ptr("table", 0), Ptr("return", 0)
        m.x["sp"] = Ptr("stack", 0)
        return aarch64.run(m, 0)

    def test_branch_on_a_message_byte_stops(self):
        from aarch64 import Unproved
        code = {0: ("ldrb", ["w8", "[x0, #3]"]), 4: ("cbz", ["w8", "c <x>"]), 8: ("nop", []), 12: ("ret", [])}
        with self.assertRaisesRegex(Unproved, "depends on data"):
            self.run_code(code)

    def test_table_index_from_a_message_byte_stops(self):
        from aarch64 import Unproved
        code = {0: ("ldrb", ["w8", "[x0, #3]"]), 4: ("ldrb", ["w9", "[x1, x8]"]), 8: ("ret", [])}
        with self.assertRaisesRegex(Unproved, "address depends on data"):
            self.run_code(code)

    def test_message_data_without_steering_runs(self):
        code = {0: ("ldrb", ["w8", "[x0, #3]"]), 4: ("eor", ["w8", "w8", "#0x5a"]), 8: ("ret", [])}
        self.run_code(code)

