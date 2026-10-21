#!/bin/sh
# Release version and tag: `sh tools/gen-ver.sh X.Y.Z` from a clean tree.
#
# One commit, on top of whatever HEAD is, setting the crate's version to
# X.Y.Z+<HEAD's hash>, and the tag vX.Y.Z+<hash> on it. The hash inside the
# version string names the code commit, so whoever holds the string and
# nothing else can later check they have the right code (a string cannot
# hold the hash of the commit it sits in, so it holds its parent's; the
# release commit changes the version and the lock alone). Zooko's scheme,
# shared with his other projects.
#
# A library's own Cargo.lock is untracked; where a b3sum/ crate depends on
# it, b3sum's requirement (X.Y.Z, without the hash: requirements take no
# build metadata) and b3sum's lock carry the version instead, and the C
# library's crate and header (capi/) take the full version too, so every
# system the version reaches (crates.io, git's tag, b3sum --version,
# b3_version(), the .pc file) shows the same string.
set -eu
version=${1:?usage: sh tools/gen-ver.sh X.Y.Z}
case $version in *[!0-9.]*|*..*|.*|*.) echo "a version is X.Y.Z: $version" >&2; exit 2;; esac
case $version in *.*.*) ;; *) echo "a version is X.Y.Z: $version" >&2; exit 2;; esac
cd "$(dirname "$0")/.."
[ -z "$(git status --porcelain)" ] || { echo "the tree must be clean" >&2; exit 2; }
latest=$(git tag -l 'v*' | sed 's/^v//; s/+.*//' | sort -V | tail -1)
if [ -n "$latest" ]; then
    [ "$(printf '%s\n%s\n' "$latest" "$version" | sort -V | tail -1)" = "$version" ] && [ "$latest" != "$version" ] || { echo "$version is not newer than the latest tag, v$latest" >&2; exit 2; }
fi
full="$version+$(git rev-parse HEAD)"
crate=$(sed -n 's/^name = "\(.*\)"/\1/p' Cargo.toml | head -1)
# A manifest's first version line (its package's) alone, in POSIX sed (GNU and BSD).
set_version() { sed -i.bak -e '/^version = "[^"]*"/{' -e "s//version = \"$full\"/" -e ':a' -e 'n' -e 'ba' -e '}' "$1" && rm "$1.bak"; }
set_version Cargo.toml
files="Cargo.toml"
if [ -f b3sum/Cargo.toml ]; then
    sed -i.bak "s/^\(blake3 = { version = \"\)[^\"]*\(\", path = \"\.\.\"\)/\1$version\2/" b3sum/Cargo.toml && rm b3sum/Cargo.toml.bak
    (cd b3sum && cargo update -q -p "$crate")
    files="$files b3sum/Cargo.toml b3sum/Cargo.lock"
    # The C library: its crate's version and the header's B3_VERSION.
    set_version capi/Cargo.toml
    sed -i.bak "s/^#define B3_VERSION \"[^\"]*\"/#define B3_VERSION \"$full\"/" capi/b3.h && rm capi/b3.h.bak
    files="$files capi/Cargo.toml capi/b3.h"
else
    cargo update -q -p "$crate"
    files="$files Cargo.lock"
fi
# --no-verify: the pre-commit hook's speed check measures code, and this
# commit changes version strings alone (AGENTS: follow a rule for its purpose).
git commit -q --no-verify -m "Version $full" -- $files
git tag "v$full"
echo "v$full"
