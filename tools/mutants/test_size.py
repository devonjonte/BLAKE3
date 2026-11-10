"""A change's check says what the change does to the size of the mutated code."""
import unittest

import check

DIFF = """diff --git a/src/a.rs b/src/a.rs
index 111..222 100644
--- a/src/a.rs
+++ b/src/a.rs
@@ -1,6 +1,7 @@
 fn kept() {}
-fn gone() {}
-// a comment that goes
+fn new_one() {
+    // a comment that comes
+
+    work();
+}
 fn also_kept() {}
diff --git a/src/b.rs b/src/b.rs
--- a/src/b.rs
+++ b/src/b.rs
@@ -3,2 +3,1 @@
-let x = 1;
-let y = 2;
+let x = 2;
"""


class Size(unittest.TestCase):
    def test_code_lines_are_counted_not_blanks_comments_or_headers(self):
        self.assertEqual(check.size_of(DIFF), (4, 3))

    def test_the_note_names_the_net_change(self):
        self.assertEqual(check.size_note(DIFF),
                         "mutants: the change adds 4 lines of code to the mutated files and removes 3 (net +1)")
        shrinking = "--- a/src/a.rs\n+++ b/src/a.rs\n@@ -1,3 +1,1 @@\n-a();\n-b();\n-c();\n+d();\n"
        self.assertEqual(check.size_note(shrinking),
                         "mutants: the change adds 1 line of code to the mutated files and removes 3 (net -2: less to test from here on)")
        self.assertEqual(check.size_note("--- a/src/a.rs\n+++ b/src/a.rs\n@@ -1,1 +1,1 @@\n-a();\n+b();\n"),
                         "mutants: the change adds 1 line of code to the mutated files and removes 1 (net 0)")

    def test_a_change_of_comments_alone_says_nothing(self):
        self.assertEqual(check.size_note("--- a/src/a.rs\n+++ b/src/a.rs\n@@ -1,1 +1,1 @@\n-// old\n+// new\n"), "")


if __name__ == "__main__":
    unittest.main()
