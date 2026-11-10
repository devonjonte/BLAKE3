"""What a change's check leaves to the whole run: a name its row already explains at
every planned place, and the kinds of mutant a sibling at the same place stands for."""
import re
import unittest

import check

P = "src/a.rs"
PLANNED = [
    f"{P}:10:5: replace * with + in area",
    f"{P}:10:5: replace * with / in area",
    f"{P}:12:9: replace | with ^ in flags",
    f"{P}:12:9: replace | with & in flags",
    f"{P}:20:3: replace < with == in below",
    f"{P}:20:3: replace < with > in below",
    f"{P}:20:3: replace < with <= in below",
    f"{P}:30:1: replace area -> u64 with 0",
    f"{P}:30:1: replace area -> u64 with 1",
    f"{P}:40:7: replace + with - in sum",
    f"{P}:44:7: replace + with - in sum",
]


def name(line):
    m = check.NAME.match(line)
    return f"{m.group(1)}\t{m.group(2)}"


class Kinds(unittest.TestCase):
    def test_each_kind_left_out_has_a_sibling_that_stays(self):
        # A kind is left out only where cargo-mutants plants another at the
        # same place: the operator it replaces must keep one replacement.
        replaced = {}
        for kind in check.SIBLING_KINDS:
            m = re.fullmatch(r"replace (\S+) with (\S+)", kind)
            self.assertIsNotNone(m, kind)
            replaced.setdefault(m.group(1), set()).add(m.group(2))
        made = {"*": {"+", "/"}, "+": {"-", "*"}, "-": {"+", "/"}, "/": {"%", "*"}, "%": {"/", "+"}, "+=": {"-=", "*="}, "-=": {"+=", "/="},
                "|": {"&", "^"}, "&": {"|", "^"}, "<": {"==", ">", "<="}, ">": {"==", "<", ">="}}
        for operator, out in replaced.items():
            self.assertIn(operator, made, operator)
            self.assertTrue(out < made[operator], f"{operator}: {out} leaves no sibling of {made[operator]}")
        # The boundary replacements stay: they are the ones an off-by-one lives behind.
        self.assertNotIn("replace < with <=", check.SIBLING_KINDS)
        self.assertNotIn("replace > with >=", check.SIBLING_KINDS)

    def test_a_kind_matches_its_own_mutants_alone(self):
        patterns = [re.compile(p) for p in check.kind_patterns()]
        out = [l for l in PLANNED if any(p.search(l) for p in patterns)]
        self.assertEqual(out, [PLANNED[1], PLANNED[2], PLANNED[4], PLANNED[5]])
        # `replace * with /` is not `replace * with /=`, nor a function's body.
        for other in [f"{P}:1:1: replace *= with /= in f", f"{P}:1:1: replace f -> u8 with 0", f"{P}:1:1: replace << with >> in f",
                      f"{P}:1:1: replace <= with > in f", f"{P}:1:1: replace >= with < in f", f"{P}:1:1: replace || with && in f"]:
            self.assertFalse(any(p.search(other) for p in patterns), other)


class Explained(unittest.TestCase):
    def test_a_name_within_its_row_at_every_planned_place_is_explained(self):
        sums = name(PLANNED[9])
        # Two planned places, a row for two: nothing new can come of it.
        self.assertEqual(check.explained(PLANNED, {sums: (2, "speed: either order")}), [sums])
        # A row for one of the two: a new place may survive, so both run.
        self.assertEqual(check.explained(PLANNED, {sums: (1, "speed: either order")}), [])
        # No row: runs.
        self.assertEqual(check.explained(PLANNED, {}), [])
        # A row for a name the change does not plant: nothing to leave out.
        self.assertEqual(check.explained(PLANNED, {f"{P}\treplace - with + in other": (3, "speed")}), [])

    def test_what_is_left_out_is_counted_once(self):
        flags = name(PLANNED[2])   # of a kind left out, and explained by its row too
        sums = name(PLANNED[9])
        kept, by_row, by_kind = check.left_to_the_whole_run(PLANNED, {flags: (1, "equivalent: disjoint bits"), sums: (2, "speed")})
        self.assertEqual(by_row, [sums, flags] if sums < flags else [flags, sums])
        self.assertEqual(kept, [PLANNED[0], PLANNED[3], PLANNED[6], PLANNED[7], PLANNED[8]])
        self.assertEqual(by_kind, 3)   # *//, <==, <>: the | with ^ is already counted with its row
        self.assertEqual(len(kept) + by_kind + 3, len(PLANNED))

    def test_every_mutant_leaves_nothing_out(self):
        self.assertEqual(check.left_to_the_whole_run(PLANNED, {}, every=True), (PLANNED, [], 0))


class OpenPool(unittest.TestCase):
    def test_a_row_of_the_pools_scheduling_is_the_pools_or_the_streams(self):
        reason = "OPEN: the pool's scheduling: by the run"
        self.assertTrue(check.open_pool("src/lanes.rs\treplace a with b in f", reason))
        self.assertTrue(check.open_pool("src/stream.rs\treplace + with - in room", reason))
        self.assertFalse(check.open_pool("src/each.rs\treplace a with b in f", reason))
        self.assertFalse(check.open_pool("src/stream.rs\treplace + with - in room", "a loop variant broken"))


if __name__ == "__main__":
    unittest.main()
