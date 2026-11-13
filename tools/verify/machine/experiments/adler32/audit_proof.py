#!/usr/bin/env python3
"""Regenerate the proof under a control and six deliberate faults, sequentially.

Run after a successful build, under a bounded process-group supervisor. Each child
has a 30-second limit. The original source/contract and checked generated files are
restored last. Only a named theorem failure counts as rejection. Timeouts are
reported separately and give overall exit status 2. OUTPUT must be new.
"""
import argparse
import os
from pathlib import Path
import subprocess
import sys

HERE = Path(__file__).resolve().parent
LANG = HERE.parents[1] / "lang"


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("out", type=Path)
    args = ap.parse_args()
    out = args.out.resolve(); out.mkdir(parents=True, exist_ok=False)
    source = HERE / "adler32.ode"
    spec = HERE / "Spec_adler32.lean"
    good, contract = source.read_text(), spec.read_text()
    env = dict(os.environ, SOURCE=str(source), ODEMOD="AdlerOde")
    timeouts = []

    def attempt(name, src, statement, accepted):
        source.write_text(src); spec.write_text(statement)
        (out / f"{name}.ode").write_text(src)
        (out / f"{name}.contract.lean").write_text(statement)
        try:
            r = subprocess.run(["timeout", "-k", "5", "30", "./prove_fn.sh", "adler32", "0x100000"], cwd=LANG,
                               env=env, text=True, capture_output=True, timeout=40)
        except subprocess.TimeoutExpired:
            raise RuntimeError(f"{name}: timeout is no proof verdict")
        log = r.stdout + r.stderr
        if (LANG / "adler32.build.log").exists(): log += (LANG / "adler32.build.log").read_text()
        (out / f"{name}.log").write_text(log)
        if r.returncode in (124, 137):
            assert not accepted, f"{name}: unchanged control timed out"
            timeouts.append(name)
            print(f"{name}: NO VERDICT (30-second deadline)", flush=True)
            return
        if accepted:
            assert r.returncode == 0 and "the compiler's proof of adler32: checked" in r.stdout, name
            # Bypass Lake's target cache for the unchanged controls.
            fresh = subprocess.run(["timeout", "-k", "5", "30", "lake", "env", "lean", "Proof_adler32.lean"],
                                   cwd=LANG, text=True, capture_output=True, timeout=40)
            (out / f"{name}.fresh.log").write_text(fresh.stdout + fresh.stderr)
            assert fresh.returncode == 0 and "sorry" not in fresh.stdout, f"{name}: fresh proof check"
            print(f"{name}: CHECKED (fresh Lean run)", flush=True)
        else:
            expected = "error: Usable.lean:" if name == "impossible-contract" else "error: Proof_adler32.lean:"
            assert r.returncode != 0 and expected in log, f"{name}: failed outside the expected theorem"
            print(f"{name}: REFUSED by {'usability' if name == 'impossible-contract' else 'machine-code proof'}", flush=True)

    try:
        attempt("unchanged-control", good, contract, True)
        mutants = [
            ("wrong-seed", good.replace("var a = 1", "var a = 2"), contract),
            ("wrong-reduction", good.replace("b = b - MOD", "b = b + MOD"), contract),
            ("overread", good.replace("u8[input + i]", "u8[input + i + 1]"), contract),
            ("wrong-packing", good.replace("b << 16", "b << 15"), contract),
            ("wrong-contract", good, contract.replace("result = checksum bytes", "result = checksum bytes + 1#64")),
            ("impossible-contract", good, contract.replace("accepts := n.toNat = bytes.length", "accepts := n.toNat = bytes.length ∧ n < n")),
        ]
        for name, src, statement in mutants:
            assert src != good or statement != contract, name
            attempt(name, src, statement, False)
    finally:
        source.write_text(good); spec.write_text(contract)
        attempt("restored-control", good, contract, True)
    if timeouts:
        print("audit incomplete: no verdict on " + ", ".join(timeouts), file=sys.stderr)
        raise SystemExit(2)


if __name__ == "__main__":
    main()
