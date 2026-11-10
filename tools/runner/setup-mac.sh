#!/bin/sh
# Sets up the benchmark runner for the hidden `benchrunner` account, then
# starts it. Run as yourself on the Mac (it asks for sudo when it needs it):
#
#     sh tools/runner/setup-mac.sh
#
# For the team's shared exchange, a Git repository, the runner's toolchain
# is named (the machine's own user may have none) and the machine labelled:
#
#     EXCHANGE_REPO=git@github.com:servil-software-factory/mac-runner.git \
#     RUNNER_TOOLCHAIN=nightly-2026-09-24 MACHINE=LABEL \
#     sh tools/runner/setup-mac.sh
#
# Safe to run again: steps already done are skipped, and runner.py is
# copied afresh each time, so this is also how to start the runner after a
# reviewed change to runner.py.
set -eu

code=$(cd "$(dirname "$0")" && pwd)
checkout=$(cd "$code/../.." && pwd)
installed=/Users/Shared/bench-runner
shared=${EXCHANGE_REPO:-}
# A label for this machine in its results' names, the operator's choice
# (never the computer's own name, which can name its owner); a shared
# exchange publishes it, so there it must be given.
machine=${MACHINE:-local}
if [ -n "$shared" ] && [ -z "${MACHINE:-}" ]; then
    echo "a shared exchange needs MACHINE=LABEL (a label of your choosing for this machine)"; exit 1
fi
if [ -n "$shared" ]; then
    # The runner's own clone of the shared exchange.
    runner=/Users/benchrunner/exchange
else
    # The exchange folder in this checkout, kept out of git by .git/info/exclude.
    runner=$checkout/runner
    grep -qx "/runner/" "$checkout/.git/info/exclude" || echo "/runner/" >> "$checkout/.git/info/exclude"
fi

step() { printf '\n== %s\n' "$*"; }

step "the benchrunner account exists"
dscl . -read /Users/benchrunner UserShell

step "Python 3"
command -v python3 >/dev/null || brew install python3
python=$(command -v python3)
"$python" --version

step "benchrunner's home is private"
sudo chmod 700 /Users/benchrunner

step "benchrunner's Rust toolchain: the very compiler you use"
# Matched by rustc's commit hash. A channel name such as `nightly` would
# install whatever is newest today. A nightly is dated a day or so after
# its rustc commit, so try the dates around it.
br_rustup="sudo -u benchrunner -H /Users/benchrunner/.cargo/bin/rustup"
br_rustc="sudo -u benchrunner -H /Users/benchrunner/.cargo/bin/rustc"
if ! sudo -u benchrunner -H test -x /Users/benchrunner/.cargo/bin/cargo; then
    sudo -u benchrunner -H sh -c "curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh -s -- -y --no-modify-path --default-toolchain none"
fi
if [ -n "${RUNNER_TOOLCHAIN:-}" ]; then
    # A named nightly, for a machine whose own user has no rustc.
    $br_rustup toolchain list | grep -q "^$RUNNER_TOOLCHAIN" || $br_rustup toolchain install --profile minimal "$RUNNER_TOOLCHAIN"
    $br_rustup default "$RUNNER_TOOLCHAIN"
    $br_rustup toolchain list | grep -v "^$RUNNER_TOOLCHAIN" | cut -d' ' -f1 | while read -r other; do $br_rustup toolchain uninstall "$other"; done
    want_hash=$($br_rustc -vV | sed -n 's/^commit-hash: //p')
else
    want_hash=$(cd ~ && rustc -vV | sed -n 's/^commit-hash: //p')
    want_date=$(cd ~ && rustc -vV | sed -n 's/^commit-date: //p')
    echo "yours: $(cd ~ && rustc --version)"
fi
if [ "$($br_rustc -vV 2>/dev/null | sed -n 's/^commit-hash: //p')" != "$want_hash" ]; then
    found=
    for shift in +1d +0d +2d +3d; do
        toolchain=nightly-$(date -j -v"$shift" -f %Y-%m-%d "$want_date" +%Y-%m-%d)
        $br_rustup toolchain install --profile minimal "$toolchain"
        got=$($br_rustup run "$toolchain" rustc -vV | sed -n 's/^commit-hash: //p')
        if [ "$got" = "$want_hash" ]; then found=$toolchain; break; fi
        $br_rustup toolchain uninstall "$toolchain"
    done
    [ -n "$found" ] || { echo "no nightly near $want_date has rustc $want_hash"; exit 1; }
    $br_rustup default "$found"
    $br_rustup toolchain list | grep -v "^$found" | cut -d' ' -f1 | while read -r other; do $br_rustup toolchain uninstall "$other"; done
fi
echo "benchrunner's: $($br_rustc --version)"
# cargo-nextest, which every test job runs (AGENTS: tests run under nextest).
if ! sudo -u benchrunner -H test -x /Users/benchrunner/.cargo/bin/cargo-nextest; then
    sudo -u benchrunner -H sh -c "curl -LsSf https://get.nexte.st/latest/mac | tar zxf - -C /Users/benchrunner/.cargo/bin"
fi
echo "benchrunner's: $(sudo -u benchrunner -H /Users/benchrunner/.cargo/bin/cargo-nextest nextest --version | head -1)"
# cargo-mutants, which a mutants job runs (tools/mutants/check.py): the VM's version.
if ! sudo -u benchrunner -H /Users/benchrunner/.cargo/bin/cargo mutants --version 2>/dev/null | grep -qx "cargo-mutants 27.1.0"; then
    sudo -u benchrunner -H /Users/benchrunner/.cargo/bin/cargo install --locked --version 27.1.0 cargo-mutants
fi
echo "benchrunner's: $(sudo -u benchrunner -H /Users/benchrunner/.cargo/bin/cargo mutants --version)"

if [ -n "$shared" ]; then
    step "the shared exchange: benchrunner's clone of $shared"
    br="sudo -u benchrunner -H"
    if ! $br test -f /Users/benchrunner/.ssh/id_ed25519.pub; then
        $br mkdir -p /Users/benchrunner/.ssh
        $br ssh-keygen -q -t ed25519 -N "" -C "benchrunner@$machine" -f /Users/benchrunner/.ssh/id_ed25519
    fi
    $br sh -c "ssh-keygen -F github.com >/dev/null 2>&1 || ssh-keyscan -t ed25519 github.com >> /Users/benchrunner/.ssh/known_hosts 2>/dev/null"
    if ! $br git -C "$runner" rev-parse --quiet --verify HEAD >/dev/null 2>&1; then
        echo "The runner's public key; add it to the exchange repository as a deploy key WITH write access, then run this again:"
        $br cat /Users/benchrunner/.ssh/id_ed25519.pub
        $br git clone --quiet "$shared" "$runner" || exit 1
    fi
    $br git -C "$runner" config user.name "Bench Runner ($machine)"
    $br git -C "$runner" config user.email "benchrunner@$machine.invalid"
    $br git -C "$runner" config pull.rebase false
    $br git -C "$runner" pull --ff-only --quiet
    sudo mkdir -p "$installed/root-probes"
    sudo chown benchrunner "$installed/root-probes"
    step "what sudo lets benchrunner run as root (tools/runner/README.md names the two lines)"
    sudo -u benchrunner sudo -n -l 2>/dev/null | grep -E 'powermetrics|root-probes' || echo "none yet: add the sudoers lines from the README"
else
    step "the exchange folder: jobs/ yours, results/ the runner's"
    chmod 600 "$checkout/ghtokenclassic.txt"
    mkdir -p "$runner/jobs" "$runner/results"
    sudo chown benchrunner "$runner/results"
    # benchrunner passes through every folder from your home down to the checkout.
    dir=$checkout
    while :; do
        ls -led "$dir" | grep -q "benchrunner allow search" || chmod +a "benchrunner allow search" "$dir"
        [ "$dir" = "$HOME" ] || [ "$dir" = / ] && break
        dir=$(dirname "$dir")
    done
    ls -le "$checkout/ghtokenclassic.txt"
    ls -led "$runner/jobs" "$runner/results"
fi

step "runner.py installed read-only for benchrunner"
sudo mkdir -p "$installed"
sudo chown "$(whoami)" "$installed"
cp "$code/runner.py" "$code/exchange.py" "$installed/"
chmod 755 "$installed"
chmod 644 "$installed/runner.py" "$installed/exchange.py"

step "benchrunner can run Python 3"
sudo -u benchrunner -H "$python" --version

step "starting the runner (Ctrl-C stops it after the current job)"
exec sudo -u benchrunner -H "$python" "$installed/runner.py" "$runner" "$machine"
