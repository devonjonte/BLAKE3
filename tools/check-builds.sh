#!/bin/sh
# The builds the Mac's and the VM's suites leave out, checked in minutes
# on this machine (part of a promotion's gate, PROCEDURES.md): the library
# without std, tested; warnings as errors for the default, pure, and
# no_sme2 builds and b3sum; and compile-only checks for x86-64 (default
# features: its C and assembly with the clang here), i686 and wasm32
# (pure); and the minimum supported Rust (MSRV, .github/workflows/ci.yml's)
# for this machine and x86-64. Each failure stops the script.
#
#     sh tools/check-builds.sh
set -eu
cd "$(git rev-parse --show-toplevel)"
export CARGO_TARGET_DIR=${CARGO_TARGET_DIR:-/tmp/target/check-builds}
msrv=1.85.1
rustup target add x86_64-unknown-linux-gnu i686-unknown-linux-gnu wasm32-wasip1 2>/dev/null
rustup toolchain install --profile minimal "$msrv" --target x86_64-unknown-linux-gnu >/dev/null 2>&1 ||
	rustup toolchain install --profile minimal "$msrv" --target x86_64-unknown-linux-gnu
step() { echo "== $*"; "$@"; }
step cargo test -q --release --no-default-features
for features in "" "--features pure" "--features no_sme2"; do
	# shellcheck disable=SC2086
	RUSTFLAGS="-D warnings" step cargo check -q --release --tests --examples $features
done
RUSTFLAGS="-D warnings" step cargo check -q --release --manifest-path b3sum/Cargo.toml
RUSTFLAGS="-D warnings" step cargo check -q --tests --examples --target x86_64-unknown-linux-gnu
RUSTFLAGS="-D warnings" step cargo check -q --tests --examples --target i686-unknown-linux-gnu --features pure
RUSTFLAGS="-D warnings" step cargo check -q --tests --target wasm32-wasip1
RUSTFLAGS="-D warnings" step cargo check -q --tests --target wasm32-wasip1 --no-default-features
# The MSRV build in a copy with a lockfile of its own, resolved for that
# compiler as CI's is (Cargo.lock is untracked; the newest versions may need
# a newer Rust).
copy=$CARGO_TARGET_DIR/msrv-src
rm -rf "$copy" && mkdir -p "$copy"
git ls-files -z | xargs -0 cp --parents -t "$copy"
(
	cd "$copy"
	CARGO_RESOLVER_INCOMPATIBLE_RUST_VERSIONS=fallback cargo +"$msrv" generate-lockfile -q
	step cargo +"$msrv" build -q --features=mmap,traits-preview,serde,zeroize
	step cargo +"$msrv" check -q --features=mmap,traits-preview,serde,zeroize --target x86_64-unknown-linux-gnu
)
echo "check-builds: every build passes"
