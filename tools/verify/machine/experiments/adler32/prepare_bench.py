#!/usr/bin/env python3
"""Make a tiny Cargo workspace from an observation and the shared clocks checkout.

    python3 prepare_bench.py CLOCKS_CHECKOUT OBSERVATION NEW_BUILD_DIRECTORY

Build with cargo build --release --manifest-path NEW_BUILD_DIRECTORY/Cargo.toml.
The executable's --validate mode reads no clock; --collect requires a measurement
machine. ODE_PADDING at build time chooses an explicit pre-function text padding.
"""
import argparse
import importlib.util
import json
from pathlib import Path
import shutil
import subprocess

HERE = Path(__file__).resolve().parent
CLOCKS_REV = "5f99f456951ab36f7201decd8aa5e0249ec67bd1"


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("clocks", type=Path)
    ap.add_argument("observation", type=Path)
    ap.add_argument("out", type=Path)
    a = ap.parse_args()
    clocks, obs, out = a.clocks.resolve(), a.observation.resolve(), a.out.resolve()
    # These are contracts for this deliberately small first workload adapter.
    r = json.loads((obs / "report.json").read_text())
    assert r["format"] == "ode-observe-v1" and r["function"] == "adler32" and r["static_calls"] == 0
    spec = importlib.util.spec_from_file_location("observe", HERE.parents[1] / "observe.py")
    observer = importlib.util.module_from_spec(spec); spec.loader.exec_module(observer)
    assert observer.digest(obs / "text.bin") == {k: r["text"][k] for k in ("sha256", "blake3")}
    assert observer.digest(obs / "source.ode") == r["source"]
    actual = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=clocks, text=True).strip()
    assert actual == CLOCKS_REV, f"clocks checkout at {CLOCKS_REV}, got {actual}"
    subprocess.run(["git", "diff", "--exit-code", "HEAD", "--", "clocks"], cwd=clocks, check=True, capture_output=True)
    out.mkdir(parents=True, exist_ok=False)
    for name in ["function.S", "text.bin", "report.json"]:
        shutil.copyfile(obs / name, out / name)
    for src, dst in [("bench.rs", "main.rs"), ("bench_build.rs", "build.rs")]:
        shutil.copyfile(HERE / src, out / dst)
    (out / "Cargo.toml").write_text(
        '[package]\nname = "ode-adler-observer"\nversion = "0.0.0"\nedition = "2021"\n'
        '[workspace]\n[[bin]]\nname = "ode-adler-observer"\npath = "main.rs"\n'
        '[dependencies]\nclocks = { path = ' + json.dumps(str(clocks / "clocks")) + ' }\n'
        '[profile.release]\ncodegen-units = 1\n')
    print(out / "Cargo.toml")


if __name__ == "__main__":
    main()
