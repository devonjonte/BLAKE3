#!/usr/bin/env python3
"""Make a tiny Cargo workspace from an observation and the shared clocks checkout.

    python3 prepare_bench.py CLOCKS_CHECKOUT PROVED_OBSERVATION PINNED_DEPS NEW_BUILD_DIRECTORY

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
DEPS = {
    "zlib": ("99623ef7097352da7993ba614161fd6a311e046e", ["-DZLIB_BUILD_SHARED=OFF", "-DZLIB_BUILD_TESTING=OFF"]),
    "zlib-ng": ("12731092979c6d07f42da27da673a9f6c7b13586", ["-DBUILD_SHARED_LIBS=OFF", "-DBUILD_TESTING=OFF", "-DZLIB_COMPAT=OFF", "-DWITH_NATIVE_INSTRUCTIONS=OFF"]),
    "libdeflate": ("92e6a0db9fa848d742f9eb286c92afc60f2c3dda", ["-DLIBDEFLATE_BUILD_SHARED_LIB=OFF", "-DLIBDEFLATE_BUILD_GZIP=OFF"]),
}


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("clocks", type=Path)
    ap.add_argument("observation", type=Path)
    ap.add_argument("deps", type=Path)
    ap.add_argument("out", type=Path)
    a = ap.parse_args()
    clocks, obs, deps, out = a.clocks.resolve(), a.observation.resolve(), a.deps.resolve(), a.out.resolve()
    # These are contracts for this deliberately small first workload adapter.
    r = json.loads((obs / "report.json").read_text())
    assert r["format"] == "ode-observe-v1" and r["function"] == "adler32" and r["static_calls"] == 0
    assert r["proof"].startswith("Lean checked Proof_adler32.adler32_meets"), "comparison requires the proved baseline"
    spec = importlib.util.spec_from_file_location("observe", HERE.parents[1] / "observe.py")
    observer = importlib.util.module_from_spec(spec); spec.loader.exec_module(observer)
    assert observer.digest(obs / "text.bin") == {k: r["text"][k] for k in ("sha256", "blake3")}
    assert observer.digest(obs / "source.ode") == r["source"]
    actual = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=clocks, text=True).strip()
    assert actual == CLOCKS_REV, f"clocks checkout at {CLOCKS_REV}, got {actual}"
    subprocess.run(["git", "diff", "--exit-code", "HEAD", "--", "clocks"], cwd=clocks, check=True, capture_output=True)
    out.mkdir(parents=True, exist_ok=False)
    for name in ["function.S", "text.bin"]:
        shutil.copyfile(obs / name, out / name)
    for name, (rev, options) in DEPS.items():
        src, build = deps / name, out / "native" / name
        actual = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=src, text=True).strip()
        assert actual == rev, (name, actual, rev)
        subprocess.run(["git", "diff", "--exit-code", "HEAD"], cwd=src, check=True, capture_output=True)
        for kind, cmd in [
            ("configure", ["cmake", "-S", str(src), "-B", str(build), "-DCMAKE_BUILD_TYPE=Release", *options]),
            ("build", ["cmake", "--build", str(build), "-j", "4"]),
        ]:
            with (out / f"{name}-{kind}.log").open("w") as log:
                subprocess.run(["timeout", "-k", "5", "240", *cmd], stdout=log, stderr=subprocess.STDOUT, check=True, timeout=250)
    r["comparison"] = {"seed": 1, "sources": {name: rev for name, (rev, _) in DEPS.items()},
                       "build": "CMake Release, each project's default optimization flags, runtime dispatch enabled, static linking, no LTO"}
    r["benchmark_files"] = {name: observer.digest(HERE / name) for name in ["bench.rs", "bench_build.rs", "prepare_bench.py"]}
    (out / "report.json").write_text(json.dumps(r, indent=2) + "\n")
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
