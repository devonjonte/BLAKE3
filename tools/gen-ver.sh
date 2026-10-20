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
# build metadata) and b3sum's lock carry the version instead.
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
sed -i.bak "0,/^version = \"[^\"]*\"/s//version = \"$full\"/" Cargo.toml && rm Cargo.toml.bak
files="Cargo.toml"
if [ -f b3sum/Cargo.toml ]; then
    sed -i.bak "s/^\(blake3 = { version = \"\)[^\"]*\(\", path = \"\.\.\"\)/\1$version\2/" b3sum/Cargo.toml && rm b3sum/Cargo.toml.bak
    (cd b3sum && cargo update -q -p "$crate")
    files="$files b3sum/Cargo.toml b3sum/Cargo.lock"
else
    cargo update -q -p "$crate"
    files="$files Cargo.lock"
fi
git commit -q -m "Version $full" -- $files
git tag "v$full"
echo "v$full"
