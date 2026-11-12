#!/usr/bin/env python3
"""tools/size.py's line counts: what counts as code, comment and test."""
import unittest

import size


class Lines(unittest.TestCase):
    def test_a_test_module_and_comments_are_apart_from_code(self):
        text = """//! A page of documentation.
use core::mem;

/// Doubles.
#[cfg(feature = "std")]
pub fn double(x: u32) -> u32 {
    if cfg!(debug_assertions) { assert!(x < 1 << 31) }
    x * 2
}

#[cfg(test)]
mod tests {
    #[test]
    fn doubles() {
        assert_eq!(super::double(2), 4);
    }
}
"""
        code, comment, test, cfg = size.split_rust(text)
        self.assertEqual((code, comment, test, cfg), (6, 2, 7, 2))

    def test_deleting_a_comment_or_a_test_leaves_code_as_it_was(self):
        with_both = "// why\nfn f() {}\n#[cfg(test)]\nmod t {\n    fn g() {}\n}\n"
        self.assertEqual(size.split_rust(with_both)[0], size.split_rust("fn f() {}\n")[0])

    def test_a_module_compiled_for_tests_alone_is_a_test_file(self):
        texts = {
            "threads/src/lib.rs": """mod lanes;
#[cfg(test)]
mod stream;
#[cfg(test)]
mod stream_tests {
    mod one_cpu;
}
#[cfg(test)]
#[path = "../../src/test_support.rs"]
pub(crate) mod test;
#[cfg(feature = "std")]
mod io;
""",
            "src/stream.rs": '#[cfg(all(feature = "std", test))]\n#[path = "stream_prototype.rs"]\nmod prototype;\n',
            "src/kernel.rs": '#[cfg(test)]\nmod test {\n    fn f() { if true {} }\n    include!("kernel_guard_tests.rs");\n}\ninclude!("tables.rs");\n',
        }
        self.assertEqual(size.test_only(texts), {
            "threads/src/stream.rs", "threads/src/stream/", "threads/src/stream_tests/",
            "src/test_support.rs", "threads/src/test/",
            "src/stream_prototype.rs", "src/stream/prototype/",
            "src/kernel_guard_tests.rs", "src/kernel/test/",
        })

    def test_a_module_under_another_condition_is_the_librarys(self):
        for attribute in ['#[cfg(feature = "std")]', "#[cfg(not(test))]", "#[cfg(any(test, debug_assertions))]", "#[allow(dead_code)]"]:
            self.assertEqual(size.test_only({"src/lib.rs": attribute + "\nmod real;\nmod plain;\n"}), set(), attribute)


class MachineCode(unittest.TestCase):
    def test_an_x86_kernel_object_is_a_kernel_whatever_its_file_is_called(self):
        """The x86-64 kernels' files have a hyphen (`x86-64`); counted by a
        name without one, 65,888 bytes of kernels went under Rust."""
        kernels = [
            "0f7afa8371890fd-blake3_sse41_x86-64_unix.o",
            "0f7afa8371890fd-blake3_avx512_x86-64_unix.o",
            "0f7afa8371890fd-blake3_chunk_root_x86-64_unix.o",
            "0f7afa8371890fd-blake3_avx512_32.o",
            "0f7afa8371890fd-blake3_output16.o",
            "db3b6bfb95261072-blake3_neon_hybrid_aarch64.o",
            "db3b6bfb95261072-blake3_sme2_aarch64.o",
        ]
        rust = [
            "blake3_servil-e4ee6835151a42ec.blake3_servil.cgu.00.rcgu.o",
            "blake3_servil-e4ee6835151a42ec.blake3_servil.cgu.15.rcgu.o",
            "lib.rmeta",
        ]
        for name in kernels:
            self.assertTrue(size.is_kernel_object(name), name)
        for name in rust:
            self.assertFalse(size.is_kernel_object(name), name)


if __name__ == "__main__":
    unittest.main()
