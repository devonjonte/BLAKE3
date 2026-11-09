"""A retained shard is writable only by the Git repository that owns it."""
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch

import check


class ShardOwner(unittest.TestCase):
    def test_a_different_clone_with_the_same_head_is_not_cleaned_or_checked_out(self):
        with tempfile.TemporaryDirectory() as d:
            home = Path(d)
            repo, foreign, trees = home / "repo", home / "foreign", home / "trees"
            repo.mkdir()
            trees.mkdir()

            def git(where, *args):
                return subprocess.run(["git", "-C", str(where), *args], check=True, capture_output=True, text=True)

            git(repo, "init", "-q")
            git(repo, "config", "user.name", "Mutation fixture")
            git(repo, "config", "user.email", "mutants@example.invalid")
            git(repo, "config", "commit.gpgsign", "false")
            (repo / "input.rs").write_text("original\n")
            git(repo, "add", "input.rs")
            git(repo, "-c", "core.hooksPath=/dev/null", "commit", "-qm", "fixture")
            git(repo, "clone", "-q", str(repo), str(foreign))
            self.assertEqual(git(repo, "rev-parse", "HEAD").stdout, git(foreign, "rev-parse", "HEAD").stdout)
            tree = trees / "run-0"
            git(foreign, "worktree", "add", "-q", "--detach", str(tree), "HEAD")
            (tree / "input.rs").write_text("foreign tracked edit\n")
            marker = tree / "foreign-untracked.txt"
            marker.write_text("keep my work\n")
            with patch.object(check, "ROOT", str(repo)), patch.object(check, "WORKTREES", str(trees)):
                with self.assertRaisesRegex(RuntimeError, "different Git repository"):
                    check.shard_tree("run", 0)
            self.assertEqual((tree / "input.rs").read_text(), "foreign tracked edit\n")
            self.assertEqual(marker.read_text(), "keep my work\n")

    def test_a_shard_whose_clone_was_deleted_is_replaced(self):
        """A runner's fresh clone, deleted after its run, leaves its shards in a shared TMPDIR:
        checkouts of nothing, which the next clone's run replaces with its own."""
        import shutil
        with tempfile.TemporaryDirectory() as d:
            home = Path(d)
            repo, gone, trees = home / "repo", home / "gone", home / "trees"
            repo.mkdir()
            trees.mkdir()

            def git(where, *args):
                return subprocess.run(["git", "-C", str(where), *args], check=True, capture_output=True, text=True)

            git(repo, "init", "-q")
            git(repo, "config", "user.name", "Mutation fixture")
            git(repo, "config", "user.email", "mutants@example.invalid")
            git(repo, "config", "commit.gpgsign", "false")
            (repo / "input.rs").write_text("original\n")
            git(repo, "add", "input.rs")
            git(repo, "-c", "core.hooksPath=/dev/null", "commit", "-qm", "fixture")
            git(repo, "clone", "-q", str(repo), str(gone))
            tree = trees / "run-0"
            git(gone, "worktree", "add", "-q", "--detach", str(tree), "HEAD")
            (tree / "left-behind.txt").write_text("the deleted clone's\n")
            shutil.rmtree(gone)
            with patch.object(check, "ROOT", str(repo)), patch.object(check, "WORKTREES", str(trees)):
                self.assertEqual(check.shard_tree("run", 0), str(tree))
            self.assertFalse((tree / "left-behind.txt").exists(), "a fresh worktree, not the orphan")
            self.assertEqual(git(tree, "rev-parse", "HEAD").stdout, git(repo, "rev-parse", "HEAD").stdout)
            self.assertIn(str(tree), git(repo, "worktree", "list").stdout, "this repository's worktree now")



if __name__ == "__main__":
    unittest.main()
