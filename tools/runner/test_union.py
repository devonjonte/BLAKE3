"""A whole run's time-outs keep the commit's rows the run did not see (BLAKE3 #380)."""
import platform
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

import runner

HEAD = ["# The mutants that time out here.", "# A line: file <TAB> mutant (function and change) <TAB> places <TAB> reason."]


def text(*rows, head=HEAD):
    return "\n".join(list(head) + list(rows)) + "\n"


POP = "src/pipeline.rs\treplace -= with += in Ring<X>::pop_front\t1\ta drain that never ends"
PUSH = "src/pipeline.rs\treplace += with -= in Ring<X>::push_back\t1\tcrashes a few tests, hangs the rest"
CUT = "src/pipeline.rs\treplace < with <= in cut_with_prefix\t2\ta plain hang"


class ListUnion(unittest.TestCase):
    def test_a_row_the_run_did_not_see_is_put_back_in_order(self):
        got, back, left = runner.list_union(text(CUT, POP, PUSH), text(PUSH))
        self.assertEqual(got, text(*sorted([CUT, POP, PUSH])))
        self.assertEqual(back, sorted([CUT, POP]))
        self.assertEqual(left, [])

    def test_a_name_both_hold_keeps_the_runs_row(self):
        newer = CUT.replace("\t2\t", "\t1\t")
        got, back, _ = runner.list_union(text(CUT), text(newer))
        self.assertEqual(got, text(newer))
        self.assertEqual(back, [])

    def test_a_new_row_stays_and_the_head_is_the_runs(self):
        new = "src/lanes.rs\tdelete ! in sources::visible\t1\tUNCLASSIFIED: times out"
        got, back, _ = runner.list_union(text(POP, head=["# an older head"]), text(new))
        self.assertEqual(got, text(*sorted([new, POP])))
        self.assertEqual(back, [POP])

    def test_rows_of_other_cpus_are_rows_of_their_own(self):
        avx2 = POP.replace("\ta drain", "\t[cpu lacks avx512f] a drain")
        wide = POP.replace("\ta drain", "\t[cpu has avx512f] a drain")
        got, back, _ = runner.list_union(text(avx2, wide), text(wide))
        self.assertEqual(got, text(*sorted([avx2, wide])))
        self.assertEqual(back, [avx2])

    def test_a_name_the_run_saw_survive_is_left_for_a_person(self):
        got, back, left = runner.list_union(text(POP, CUT), text(), survived={("src/pipeline.rs", "replace -= with += in Ring<X>::pop_front")})
        self.assertEqual(got, text(CUT))
        self.assertEqual((back, left), ([CUT], [POP]))

    def test_a_list_the_commit_does_not_hold_has_nothing_to_put_back(self):
        self.assertEqual(runner.list_union("", text(POP)), (text(POP), [], []))


class Checkout:
    """A checkout whose check.py --write is played by `write`."""
    def __init__(self, root, write):
        self.root, self.write = root, write

    def checkouts(self, *_):
        return self.root, None

    def run(self, command, cwd=None, capture=False, **_):
        if command[:2] == [sys.executable, "tools/mutants/check.py"]:
            self.write()
            return ""
        return subprocess.run(command, cwd=cwd, check=True, stdout=subprocess.PIPE, text=True).stdout


class WholeRun(unittest.TestCase):
    def test_the_job_returns_the_union_and_says_what_it_put_back(self):
        with tempfile.TemporaryDirectory() as d:
            root, out = Path(d) / "fork", Path(d) / "out"
            lists = root / "tools" / "mutants" / "threads"
            lists.mkdir(parents=True)
            out.mkdir()
            known, timeouts = (lists / f"{kind}-{platform.machine()}.txt" for kind in ("known", "timeouts"))
            survivor = "src/lanes.rs\tdelete ! in initialize\t1\tOPEN: the pool's scheduling"
            known.write_text(text(survivor))
            timeouts.write_text(text(*sorted([CUT, POP, PUSH])))
            git = lambda *a: subprocess.run(["git", "-c", "user.name=t", "-c", "user.email=t@example.org", *a], cwd=root, check=True, stdout=subprocess.DEVNULL)
            git("init", "-q")
            git("add", "-A")
            git("commit", "-q", "-m", "lists")
            # this run: the pop mutant crashed first (no time-out), and the cut one survived at one place
            cut_survives = CUT.replace("\t2\ta plain hang", "\t1\tUNCLASSIFIED: survives")
            def write():
                known.write_text(text(survivor, cut_survives))
                timeouts.write_text(text(PUSH))
            verdict = runner.mutants_whole({"crate": "threads", "fork_commit": "0" * 40}, Checkout(root, write), None, out)
            self.assertEqual(verdict, "no new survivor")
            self.assertEqual((out / "lists" / timeouts.name).read_text(), text(*sorted([POP, PUSH])))
            self.assertEqual((out / "lists-written" / timeouts.name).read_text(), text(PUSH))
            self.assertEqual((out / "lists" / known.name).read_text(), text(*sorted([survivor, cut_survives])))
            self.assertEqual((out / "lists-put-back.txt").read_text(),
                             f"put back\t{POP}\nNOT put back: this run saw it survive\t{CUT}\n")
            diff = (out / "lists-diff.txt").read_text()
            self.assertIn("-" + CUT, diff)
            self.assertNotIn("-" + POP, diff)


if __name__ == "__main__":
    unittest.main()
