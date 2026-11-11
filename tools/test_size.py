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


if __name__ == "__main__":
    unittest.main()
