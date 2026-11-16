#!/bin/sh
# tools/b3sum-release.sh in a new Ubuntu 26.04 container, as root: installs
# what tools/b3sum-release.toolchain names and runs it. How GitHub's
# machines build b3sum's release binary (.github/workflows), and how
# anyone can, with Docker or Podman, from a clone at a release's tag:
#
#     docker run --rm -v "$PWD":/src -w /src ubuntu:26.04 sh tools/b3sum-release-container.sh
#
# The binary and its digests are then in dist/: the same bytes as the
# release's, or the release's was not built from this source.
set -eu
want() { sed -n "s/^$1 //p" tools/b3sum-release.toolchain; }
export DEBIAN_FRONTEND=noninteractive
apt="apt-get -q -o Acquire::Retries=3 -o Acquire::http::Timeout=60 -o Acquire::https::Timeout=60"
$apt update
$apt install -y --no-install-recommends ca-certificates git curl clang file python3
# The C library the toolchain file names: from Ubuntu's archive while it
# is the current one there, and after that from the archive's snapshot of
# the day the file names.
libc=$(want libc6-dev)
libc="libc6-dev=$libc libc-dev-bin=$libc libc6=$libc libc-bin=$libc"
# shellcheck disable=SC2086
$apt install -y --no-install-recommends --allow-downgrades $libc || {
	$apt update --snapshot "$(want apt-snapshot)"
	# shellcheck disable=SC2086
	$apt install -y --no-install-recommends --allow-downgrades --snapshot "$(want apt-snapshot)" $libc
}
curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh -s -- -y --profile minimal --default-toolchain "$(want rustc)"
. "$HOME/.cargo/env"
git config --global --add safe.directory '*'
sh tools/b3sum-release.sh
