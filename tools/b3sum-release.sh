#!/bin/sh
# b3sum's release binary for this machine, built from a fresh clone of the
# release tag's commit: statically linked on Linux (the recommended build,
# b3sum/README.md), as the platform links elsewhere (macOS). Writes
# dist/b3sum-VERSION-TARGET and its SHA-256 and BLAKE3 digests beside it,
# for a GitHub release (CONTRIBUTING.md, "Releases").
#
#     sh tools/b3sum-release.sh
#
# A fresh clone, since a binary is built from every file of its checkout
# that Git does not ignore, and a working checkout holds more than the
# commit. 0.9.0's two binaries were built where logs and worktrees lay
# untracked, and their versions say "dirty" (BLAKE3 #435). The clone holds
# the commit and nothing else, whatever this checkout holds; and the
# binary's own build version is then read (tools/release_artifacts.py):
# without the release's version alone in it, no file is left in dist/.
set -eu
cd "$(git rev-parse --show-toplevel)"
version=$(git describe --tags --exact-match 2>/dev/null) || { echo "b3sum-release: HEAD is no release tag" >&2; exit 1; }
target=$(rustc -vV | sed -n 's/^host: //p')
stage="target/b3sum-release/$version"
rm -rf "$stage"
git clone --quiet --no-checkout . "$stage/source"
git -C "$stage/source" checkout --quiet --detach "$(git rev-parse HEAD)"
case "$target" in
	*-linux-gnu) export RUSTFLAGS="-C target-feature=+crt-static" ;;
esac
cargo build --release --locked --manifest-path "$stage/source/b3sum/Cargo.toml" --target "$target" --target-dir "$stage/target"
mkdir -p dist
out="dist/b3sum-$version-$target"
cp "$stage/target/$target/release/b3sum" "$out"
python3 tools/release_artifacts.py "$version" "$out" || { rm -f "$out"; exit 1; }
# The binary checks itself against BLAKE3's published digest of nothing.
test "$(printf '' | "$out" --no-names)" = af1349b9f5f9a1a6a0404dea36dcc9499bcb25c9adc112b7cc9a93cae41f3262
name=$(basename "$out")
(cd dist && { sha256sum "$name" 2>/dev/null || shasum -a 256 "$name"; } > "$name.sha256" && "./$name" "$name" > "$name.b3")
file "$out"
echo "b3sum-release: $out, with .sha256 and .b3 beside it"
