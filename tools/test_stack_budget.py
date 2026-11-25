#!/usr/bin/env python3
"""Unit tests for tools/stack_budget.py."""

import unittest

import stack_budget


SAMPLE_FUNCS_FIRST = """
StackSizes [
  Entry {
    Functions: [_ZN18blake3_servil_core4tree9hash_tree17h0000000000000000E]
    Size: 0x2000
  }
  Entry {
    Functions: [_ZN18blake3_servil_core11convenience6Hasher8finalize17h0000000000000000E]
    Size: 0x1000
  }
  Entry {
    Functions: [_ZN13blake3_servil5lanes8run_work17h0000000000000000E]
    Size: 0x800
  }
  Entry {
    Functions: [_ZN6b3sums4main17h0000000000000000E]
    Size: 0x400
  }
]
"""

SAMPLE_SIZE_FIRST = """
StackSizes [
  Entry {
    Size: 0x4001
    Functions: [_ZN13blake3_servil5lanes8too_big17h0000000000000000E]
  }
]
"""


class StackBudgetTests(unittest.TestCase):
    def test_parses_and_passes_under_caps(self) -> None:
        entries = stack_budget.parse_llvm_readobj_stack_sizes(SAMPLE_FUNCS_FIRST)
        self.assertEqual(len(entries), 4)
        max_by_bucket, violations = stack_budget.check_entries(entries)
        self.assertEqual(violations, [])
        self.assertEqual(max_by_bucket["core"][0], 0x2000)
        self.assertEqual(max_by_bucket["core::Hasher"][0], 0x1000)
        self.assertEqual(max_by_bucket["threads"][0], 0x800)
        self.assertEqual(max_by_bucket["b3sum"][0], 0x400)

    def test_fails_when_threads_exceeds_16k(self) -> None:
        entries = stack_budget.parse_llvm_readobj_stack_sizes(SAMPLE_SIZE_FIRST)
        _, violations = stack_budget.check_entries(entries)
        self.assertEqual(len(violations), 1)
        self.assertIn("threads:", violations[0])
        self.assertIn("16385 B > 16384 B", violations[0])

    def test_fails_when_hasher_exceeds_32k(self) -> None:
        entries = [(32 * 1024 + 8, "_ZN18blake3_servil_core11convenience6Hasher8finalizeE")]
        _, violations = stack_budget.check_entries(entries)
        self.assertEqual(len(violations), 1)
        self.assertIn("core::Hasher:", violations[0])

    def test_fails_when_core_exceeds_128k(self) -> None:
        entries = [(128 * 1024 + 16, "_ZN18blake3_servil_core4tree8too_deepE")]
        _, violations = stack_budget.check_entries(entries)
        self.assertEqual(len(violations), 1)
        self.assertIn("core:", violations[0])

    def test_ignores_address_size_header_and_empty_functions_entry(self) -> None:
        sample = """
File: target/stack-budget/release/b3sum
Format: elf64-x86-64
Arch: x86_64
AddressSize: 64bit
StackSizes [
  Entry {
    Functions: []
    Size: 0x10
  }
  Entry {
    Functions: [_RNvNtCs760tuxHRkot_13blake3_servil5lanes8too_big]
    Size: 0x5000
  }
  Entry {
    Functions: [_RNvNtCs6LKpzGEycGt_18blake3_servil_core4tree5small]
    Size: 0x40
  }
]
"""
        entries = stack_budget.parse_llvm_readobj_stack_sizes(sample)
        self.assertEqual(
            entries,
            [
                (0x5000, "_RNvNtCs760tuxHRkot_13blake3_servil5lanes8too_big"),
                (0x40, "_RNvNtCs6LKpzGEycGt_18blake3_servil_core4tree5small"),
            ],
        )
        _, violations = stack_budget.check_entries(entries)
        self.assertEqual(len(violations), 1)
        self.assertIn("threads:", violations[0])

    def test_classifies_threads_symbol_with_core_type_arg_as_threads(self) -> None:
        sym = "_RNvMsr_NtCs760tuxHRkot_13blake3_servil8pipelineINtB5_8PipelinejuNtNtCs6LKpzGEycGt_18blake3_servil_core5block5BatchE12poll_message"
        self.assertEqual(stack_budget.classify_symbol(sym), ("threads", stack_budget.CAP_THREADS))
        _, violations = stack_budget.check_entries([(24 * 1024, sym)])
        self.assertEqual(len(violations), 1)
        self.assertIn("threads:", violations[0])

    def test_tree_hasher_not_classified_as_incremental_hasher(self) -> None:
        sym = "_RNvMs0_NtCs6LKpzGEycGt_18blake3_servil_core10throughput10TreeHasher9hash_each"
        self.assertEqual(stack_budget.classify_symbol(sym), ("core", stack_budget.CAP_CORE_B3SUM))


if __name__ == "__main__":
    unittest.main()
