"""The crate's version: a release's, the code after it, and the check.

    python3 tools/gen-ver.py X.Y.Z    # a release, from a clean tree
    python3 tools/gen-ver.py --dev    # the code after a release: X.Y.Z+dev
    python3 tools/gen-ver.py --check  # the version names this commit truly

One commit, on top of whatever HEAD is, setting the crate's version to
X.Y.Z+<HEAD's hash>, and the tag vX.Y.Z+<hash> on it. The hash inside the
version string names the code commit, so whoever holds the string and
nothing else can later check they have the right code (a string cannot
hold the hash of the commit it sits in, so it holds its parent's; the
release commit changes version strings alone). Zooko's scheme, shared
with his other projects.

Every copy of the version carries it in full, hash included, whether or
not today's tools check it, since future tools may (Zooko, October 20):
the crate (crates.io, its docs) and its build version's crate
(version/, its exact dependency), the tag, and, where the repository has
them, the CHANGELOG's title, b3sum's own version (`b3sum --version`) and
its exact requirement on the crate (`=X.Y.Z+<hash>`: Cargo reads it up to
the `+` today, and warns), the C library's crate (`b3_version()`), header
(`B3_VERSION`); cargo-c generates the pkg-config version from the crate.
The soname alone takes X.Y: its format holds digits and dots.

A release's version names its code, so the commits after it must not keep
it: the first change after a release, on any branch, sets X.Y.Z+dev
(`--dev`, in every copy but the CHANGELOG's title, which names the
release its notes describe). A reader who knows the releases then reads "newer
than X.Y.Z" in the version alone (bench-hashes' map shows it so). `--check`
holds the rule, run by tools/check-builds.sh: the version is X.Y.Z+dev, or
X.Y.Z+<hash> on the commit whose parent is <hash> (the release commit).
"""
import os
import re
import subprocess
import sys


def git(*args):
    return subprocess.run(["git", *args], check=True, capture_output=True, text=True).stdout.strip()


def edit(path, pattern, replacement):
    """Replace the first line matching `pattern`; stop if none does."""
    with open(path) as f:
        text, n = re.subn(pattern, replacement, f.read(), count=1, flags=re.M)
    if n != 1:
        sys.exit(f"{path}: no line matches {pattern}")
    with open(path, "w") as f:
        f.write(text)


RELEASE = re.compile(r"(\d+\.\d+\.\d+)\+([0-9a-f]{40}|dev)")


def current():
    """The crate's version, split: its release number and its +part."""
    version = re.search(r'^version = "(.*)"$', open("Cargo.toml").read(), re.M).group(1)
    m = RELEASE.fullmatch(version)
    if not m:
        sys.exit(f"Cargo.toml's version {version!r} is neither X.Y.Z+<commit> nor X.Y.Z+dev")
    return m.group(1), m.group(2)


def set_version(full, notes=True):
    """Every copy of the version set to `full` (and the CHANGELOG's title
    where `notes`: a release's notes name it): the files it changed."""
    crate = re.search(r'^name = "(.*)"$', open("Cargo.toml").read(), re.M).group(1)
    edit("Cargo.toml", r'^version = ".*"$', f'version = "{full}"')
    # The build version's crate (version/) goes with the library, exactly.
    edit("Cargo.toml", r'^(blake3-servil-version = \{ version = ")[^"]*', rf"\g<1>={full}")
    edit("version/Cargo.toml", r'^version = ".*"$', f'version = "{full}"')
    files = ["Cargo.toml", "version/Cargo.toml"]
    if notes and os.path.exists("CHANGELOG.md"):
        edit("CHANGELOG.md", rf"^# {crate} [^\s,]+", f"# {crate} {full}")
        files.append("CHANGELOG.md")
    if os.path.exists("b3sum/Cargo.toml"):
        edit("b3sum/Cargo.toml", r'^version = ".*"$', f'version = "{full}"')
        edit("b3sum/Cargo.toml", r'^(blake3 = \{ version = ")[^"]*', rf"\g<1>={full}")
        subprocess.run(["cargo", "update", "-q", "-p", crate, "-p", "blake3-servil-version", "-p", "b3sums"], cwd="b3sum", check=True)
        edit("capi/Cargo.toml", r'^version = ".*"$', f'version = "{full}"')
        edit("capi/b3.h", r'^#define B3_VERSION ".*"$', f'#define B3_VERSION "{full}"')
        files += ["b3sum/Cargo.toml", "b3sum/Cargo.lock", "capi/Cargo.toml", "capi/b3.h"]
    else:
        subprocess.run(["cargo", "update", "-q", "-p", crate], check=True)
        files.append("Cargo.lock")
    return crate, files


os.chdir(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
if sys.argv[1:] == ["--check"]:
    release, named = current()
    if named != "dev" and git("rev-parse", "HEAD^") != named:
        sys.exit(f"the version {release}+{named[:12]} names a release's code, and this commit is past that release's: "
                 f"set {release}+dev (python3 tools/gen-ver.py --dev)")
    sys.exit(0)
if sys.argv[1:] == ["--dev"]:
    if git("status", "--porcelain"):
        sys.exit("the tree must be clean")
    release, named = current()
    if named == "dev":
        sys.exit(f"the version is {release}+dev already")
    full = f"{release}+dev"
    _, files = set_version(full, notes=False)
    git("commit", "-q", "--no-verify", "-m", f"Version {full}: the code after {release}", "--", *files)
    print(full)
    sys.exit(0)
if len(sys.argv) != 2 or not re.fullmatch(r"\d+\.\d+\.\d+", sys.argv[1]):
    sys.exit("usage: python3 tools/gen-ver.py X.Y.Z | --dev | --check")
version = sys.argv[1]
if git("status", "--porcelain"):
    sys.exit("the tree must be clean")
number = lambda v: tuple(map(int, v.split("+")[0].split(".")))
tags = [number(t[1:]) for t in git("tag", "-l", "v*").split()]
if tags and number(version) <= max(tags):
    sys.exit(f"{version} is not newer than the latest tag, v{'.'.join(map(str, max(tags)))}")

full = f"{version}+{git('rev-parse', 'HEAD')}"
crate, files = set_version(full)
# --no-verify: the pre-commit hook's speed check measures code, and this
# commit changes version strings alone (AGENTS: follow a rule for its purpose).
git("commit", "-q", "--no-verify", "-m", f"Version {full}", "--", *files)
git("tag", f"v{full}")
print(f"v{full}")
# The dependency line for the release notes: the release commit by its full
# hash, which Cargo fetches exactly, and the full version.
print(f'{crate} = {{ git = "{git("remote", "get-url", "origin")}", rev = "{git("rev-parse", "HEAD")}", version = "={full}" }}')
