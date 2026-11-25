"""A change's shards: today's count everywhere it was measured, more only
where the machine has the CPUs and the memory and the change has the mutants,
and sibling shard process-group cleanup when a shard fails or is interrupted."""
import os
import subprocess
import sys
import tempfile
import time
import unittest

import check

GIB = 1 << 30


class Wide(unittest.TestCase):
    def test_a_machine_the_six_were_chosen_on_keeps_six(self):
        # The VM and the Mac (16 CPUs), the i7-12700K (20), a 9700X (16).
        for cpus, memory in [(16, 57 * GIB), (20, 14 * GIB), (20, 64 * GIB), (16, 128 * GIB), (1, 2 * GIB)]:
            self.assertEqual(check.wide_shards(cpus, memory), check.SHARDS, (cpus, memory))

    def test_more_cpus_give_a_shard_for_every_four(self):
        self.assertEqual(check.wide_shards(48, 396 * GIB), 12)   # the EPYC 9255
        self.assertEqual(check.wide_shards(56, 512 * GIB), 14)
        self.assertEqual(check.wide_shards(27, 512 * GIB), 6)    # 27 // 4 = 6

    def test_memory_bounds_them_at_the_cap_six_have(self):
        # Each added shard's processes keep the 8 GiB data cap: 68 GiB less
        # 4 GiB holds eight such shards, whatever the CPUs.
        self.assertEqual(check.wide_shards(96, 68 * GIB), 8)
        self.assertEqual(check.wide_shards(96, 30 * GIB), check.SHARDS)
        for cpus, memory in [(48, 396 * GIB), (96, 68 * GIB), (56, 512 * GIB)]:
            shards = check.wide_shards(cpus, memory)
            self.assertEqual(min(8 * GIB, (memory - 4 * GIB) // shards), 8 * GIB, (cpus, memory))


class Count(unittest.TestCase):
    def test_up_to_six_the_rule_is_the_one_it_was(self):
        for wide in [6, 12, 24]:
            for mutants in range(0, 48):
                self.assertEqual(check.shard_count(mutants, wide), min(check.SHARDS, max(1, mutants // 3)), (mutants, wide))

    def test_without_room_nothing_changes(self):
        for mutants in [0, 1, 17, 37, 163, 1070]:
            self.assertEqual(check.shard_count(mutants, check.SHARDS), min(check.SHARDS, max(1, mutants // 3)))

    def test_added_shards_each_have_eight_mutants(self):
        self.assertEqual(check.shard_count(37, 12), 6)      # the #326 change: as it was
        self.assertEqual(check.shard_count(55, 12), 6)
        self.assertEqual(check.shard_count(56, 12), 7)
        self.assertEqual(check.shard_count(100, 12), 12)
        self.assertEqual(check.shard_count(163, 12), 12)    # the measured change
        self.assertEqual(check.shard_count(163, 24), 20)
        for wide in [7, 12, 14, 24]:
            for mutants in range(48, 400):
                shards = check.shard_count(mutants, wide)
                self.assertTrue(check.SHARDS <= shards <= wide)
                self.assertTrue(shards == check.SHARDS or mutants // shards >= 8, (mutants, wide, shards))


class Cleanup(unittest.TestCase):
    @staticmethod
    def _alive(pid):
        try:
            os.kill(pid, 0)
            return True
        except ProcessLookupError:
            return False

    def _wait_dead(self, pid, timeout=3.0):
        deadline = time.monotonic() + timeout
        while time.monotonic() < deadline:
            if not self._alive(pid):
                return True
            time.sleep(0.05)
        return not self._alive(pid)

    def test_run_shards_kills_sibling_process_groups_and_clears_incremental_on_failure(self):
        # Shard 0 spawns a long-lived child in its process group while shard 1
        # fails baseline twice (rc=4): run_shards must fail fast without waiting
        # for shard 0, terminate both shard 0 and its child, and wipe only the
        # interrupted shard's incremental dir.
        with tempfile.TemporaryDirectory() as tmp:
            t0, t1 = os.path.join(tmp, "s0"), os.path.join(tmp, "s1")
            tgt0, tgt1 = os.path.join(tmp, "tgt0"), os.path.join(tmp, "tgt1")
            inc0 = os.path.join(tgt0, "mutants", "incremental")
            os.makedirs(t0)
            os.makedirs(t1)
            os.makedirs(inc0)
            with open(os.path.join(inc0, "partial.o"), "wb"):
                pass
            pidfile = os.path.join(tmp, "child.pid")
            shard0 = ["sh", "-c", f"sleep 30 & pid=$!; echo $pid > {pidfile}.tmp && mv {pidfile}.tmp {pidfile}; wait"]
            shard1 = [
                sys.executable,
                "-c",
                f"import os, sys, time\n"
                f"deadline = time.monotonic() + 5.0\n"
                f"while not os.path.exists({pidfile!r}) and time.monotonic() < deadline:\n"
                f"    time.sleep(0.02)\n"
                f"sys.exit(4)\n",
            ]
            envs = {
                t0: dict(os.environ, CARGO_TARGET_DIR=tgt0),
                t1: dict(os.environ, CARGO_TARGET_DIR=tgt1),
            }
            started = time.monotonic()
            with self.assertRaises(AssertionError):
                check.run_shards([(t0, shard0), (t1, shard1)], envs, shards=2, cwd_fn=lambda t: t, grace=1.0)
            elapsed = time.monotonic() - started
            self.assertLess(elapsed, 5.0, "failing shard 1 must abort running shard 0 immediately")
            self.assertTrue(os.path.exists(pidfile), "shard 0 spawned its child before shard 1 failed")
            with open(pidfile) as f:
                child_pid = int(f.read().strip())
            self.assertTrue(self._wait_dead(child_pid), f"grandchild {child_pid} left alive after shard failure")
            self.assertFalse(os.path.exists(inc0), "interrupted shard incremental cache cleared")

    def test_stop_shards_escalates_to_sigkill_and_leaves_finished_caches_alone(self):
        with tempfile.TemporaryDirectory() as tmp:
            done_tree, hung_tree = os.path.join(tmp, "done"), os.path.join(tmp, "hung")
            done_tgt, hung_tgt = os.path.join(tmp, "tgt-done"), os.path.join(tmp, "tgt-hung")
            done_inc = os.path.join(done_tgt, "mutants", "incremental")
            hung_inc = os.path.join(hung_tgt, "mutants", "incremental")
            for d in (done_tree, hung_tree, done_inc, hung_inc):
                os.makedirs(d)
            done_proc = subprocess.Popen([sys.executable, "-c", "pass"], **check.shard_spawn_kwargs(2))
            done_proc.wait()
            ready = os.path.join(tmp, "ready")
            hung_proc = subprocess.Popen(
                ["sh", "-c", f"trap '' TERM; : > {ready}; sleep 30"],
                **check.shard_spawn_kwargs(2),
            )
            deadline = time.monotonic() + 3.0
            while not os.path.exists(ready) and time.monotonic() < deadline:
                time.sleep(0.02)
            check.stop_shards(
                [(done_tree, done_proc), (hung_tree, hung_proc)],
                grace=0.2,
                clear_incremental={done_tree: done_tgt, hung_tree: hung_tgt},
            )
            self.assertIsNotNone(hung_proc.poll(), "SIGTERM-ignoring shard killed via SIGKILL")
            self.assertTrue(os.path.exists(done_inc), "already-finished shard incremental cache kept")
            self.assertFalse(os.path.exists(hung_inc), "killed shard incremental cache cleared")


if __name__ == "__main__":
    unittest.main()
