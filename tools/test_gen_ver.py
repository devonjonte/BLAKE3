"""Version stamping in disposable repositories: no release or registry upload.

Cargo resolves four tiny path packages and writes their real lockfile. The
fixtures have no registry dependencies and never compile code.
"""
from pathlib import Path
import os
import shutil
import subprocess
import tempfile
import unittest

SCRIPT = Path(__file__).with_name("gen-ver.py")
DEV = "0.8.0+dev"
MANIFESTS = {
    "version/Cargo.toml": ("blake3-servil-version", ""),
    "Cargo.toml": ("blake3-servil-core", 'blake3-servil-version = { version = "=0.8.0+dev", path = "version" }'),
    "threads/Cargo.toml": ("blake3-servil", 'blake3-servil-core = { version = "=0.8.0+dev", path = ".." }'),
    "b3sum/Cargo.toml": ("b3sums", 'blake3 = { version = "=0.8.0+dev", path = "../threads", package = "blake3-servil" }'),
    "capi/Cargo.toml": ("blake3-servil-c", 'blake3-servil = { path = "..", package = "blake3-servil-core" }'),
}


class Versions(unittest.TestCase):
    def setUp(self):
        tmp = tempfile.TemporaryDirectory(dir="/dev/shm" if Path("/dev/shm").is_dir() else None)
        self.addCleanup(tmp.cleanup)
        self.root = Path(tmp.name)
        for path, (name, dependency) in MANIFESTS.items():
            manifest = self.root / path
            manifest.parent.mkdir(parents=True, exist_ok=True)
            manifest.write_text(f'[package]\nname = "{name}"\nversion = "{DEV}"\nedition = "2024"\n[dependencies]\n{dependency}\n')
            src = manifest.parent / "src"
            src.mkdir()
            (src / "lib.rs").write_text("")
        (self.root / "tools").mkdir()
        shutil.copyfile(SCRIPT, self.root / "tools/gen-ver.py")
        (self.root / "CHANGELOG.md").write_text("# blake3-servil 0.8.0+" + "a" * 40 + ", against official BLAKE3\n")
        (self.root / "capi/b3.h").write_text(f'#define B3_VERSION "{DEV}"\n')
        self.run_command("cargo", "generate-lockfile", "--offline", "--manifest-path", "b3sum/Cargo.toml")
        self.git("init", "-q")
        self.git("config", "user.name", "Version test")
        self.git("config", "user.email", "version-test@example.invalid")
        self.git("config", "core.hooksPath", str(self.root / "no-hooks"))
        self.git("config", "commit.gpgsign", "false")
        self.git("remote", "add", "origin", "https://example.invalid/repo")
        self.git("add", ".")
        self.git("commit", "-qm", "fixture")

    def run_command(self, *args):
        return subprocess.run(args, cwd=self.root, text=True, capture_output=True, check=True,
                              env=dict(os.environ, CARGO_NET_OFFLINE="true")).stdout.strip()

    def git(self, *args):
        return self.run_command("git", *args)

    def stamp(self, arg, succeeds=True):
        result = subprocess.run(["python3", "tools/gen-ver.py", arg], cwd=self.root,
                                text=True, capture_output=True,
                                env=dict(os.environ, CARGO_NET_OFFLINE="true"))
        self.assertEqual(result.returncode == 0, succeeds, result.stdout + result.stderr)
        return result.stdout + result.stderr

    def test_release_and_dev_update_every_copy_and_lock(self):
        self.stamp("--check")
        parent = self.git("rev-parse", "HEAD")
        full = "99.1.2+" + parent
        output = self.stamp("99.1.2")
        version_commit = self.git("rev-parse", "HEAD")
        self.assertEqual(self.git("rev-parse", "HEAD^"), parent)
        self.assertEqual(self.git("rev-parse", "v" + full), version_commit)
        self.assertIn(f'blake3-servil-core = {{ git = "https://example.invalid/repo", rev = "{version_commit}", version = "={full}" }}', output)
        self.assertIn(f'blake3-servil = {{ git = "https://example.invalid/repo", rev = "{version_commit}", version = "={full}" }}', output)
        for path in MANIFESTS:
            self.assertIn(f'version = "{full}"', (self.root / path).read_text())
        self.assertEqual((self.root / "b3sum/Cargo.lock").read_text().count(f'version = "{full}"'), 4)
        notes = (self.root / "CHANGELOG.md").read_text()
        self.assertTrue(notes.startswith(f"# blake3-servil {full},"))
        self.assertEqual(self.git("status", "--porcelain"), "")
        self.stamp("--check")
        self.git("commit", "--allow-empty", "-qm", "after the release")
        self.assertIn("past that release", self.stamp("--check", succeeds=False))
        self.stamp("--dev")
        self.stamp("--check")
        for path in MANIFESTS:
            self.assertIn('version = "99.1.2+dev"', (self.root / path).read_text())
        self.assertEqual((self.root / "CHANGELOG.md").read_text(), notes)
        self.assertEqual(self.git("status", "--porcelain"), "")

    def test_check_rejects_each_stale_copy(self):
        cases = [(path, f'version = "{DEV}"') for path in MANIFESTS if path != "Cargo.toml"]
        cases += [(path, f'version = "={DEV}"') for path in ("Cargo.toml", "threads/Cargo.toml", "b3sum/Cargo.toml")]
        cases += [("capi/b3.h", DEV), ("b3sum/Cargo.lock", DEV)]
        for path, old in cases:
            with self.subTest(path=path, old=old):
                file = self.root / path
                original = file.read_text()
                file.write_text(original.replace(old, old.replace(DEV, "0.7.0+dev"), 1))
                self.assertIn(path, self.stamp("--check", succeeds=False))
                file.write_text(original)
        self.stamp("--check")

    def test_dirty_tree_is_unchanged(self):
        file = self.root / "threads/src/lib.rs"
        file.write_text("// unfinished work\n")
        before = self.git("diff", "HEAD")
        self.assertIn("tree must be clean", self.stamp("99.1.2", succeeds=False))
        self.assertEqual(self.git("diff", "HEAD"), before)
        self.assertEqual(self.git("tag", "-l"), "")

    def test_version_must_advance(self):
        self.git("tag", "v99.1.2+" + "a" * 40)
        before = self.git("rev-parse", "HEAD")
        self.assertIn("not newer", self.stamp("99.1.2", succeeds=False))
        self.assertEqual(self.git("rev-parse", "HEAD"), before)
        self.assertEqual(self.git("status", "--porcelain"), "")


if __name__ == "__main__":
    unittest.main()
