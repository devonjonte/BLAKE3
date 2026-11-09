"""A change's shards: today's count everywhere it was measured, more only
where the machine has the CPUs and the memory and the change has the mutants."""
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


if __name__ == "__main__":
    unittest.main()
