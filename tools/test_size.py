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


if __name__ == "__main__":
    unittest.main()
