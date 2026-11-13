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
ISAL_REV = "7c3479e0a9dac17f448603ec1ad64c7c625f530c"
DEPS = {
    "zlib": ("99623ef7097352da7993ba614161fd6a311e046e", ["-DZLIB_BUILD_SHARED=OFF", "-DZLIB_BUILD_TESTING=OFF"]),
    "zlib-ng": ("12731092979c6d07f42da27da673a9f6c7b13586", ["-DBUILD_SHARED_LIBS=OFF", "-DBUILD_TESTING=OFF", "-DZLIB_COMPAT=OFF", "-DWITH_NATIVE_INSTRUCTIONS=OFF"]),
    "libdeflate": ("92e6a0db9fa848d742f9eb286c92afc60f2c3dda", ["-DLIBDEFLATE_BUILD_SHARED_LIB=OFF", "-DLIBDEFLATE_BUILD_GZIP=OFF"]),
}


def verify_archive_sections(archive, exposed):
    # objdump includes every archive member, including duplicate member names.
    # -s includes allocated code/data and read-only constants; -h also covers
    # zero-filled sections. Relocations must remain the same as well.
    for flag in ["-s", "-h", "-r"]:
        def snapshot(path):
            return subprocess.check_output(["objdump", flag, path], text=True).replace(str(path), "ARCHIVE")
        before, after = snapshot(archive), snapshot(exposed)
        assert before == after, f"experimental libdeflate exposure changed {flag}"


def expose_libdeflate(archive, out, observer):
    """Globalize two experimental bindings in a copy; retain every section byte."""
    exposed = archive.with_name("libdeflate-wide.a")
    symbols = ["adler32_x86_avx512_vl512_vnni", "adler32_impl"]
    subprocess.run(["objcopy", *["--globalize-symbol=" + s for s in symbols], archive, exposed], check=True)
    verify_archive_sections(archive, exposed)
    globals_ = subprocess.check_output(["nm", "-g", "--defined-only", exposed], text=True)
    assert all(any(line.split()[-1:] == [s] for line in globals_.splitlines()) for s in symbols)
    evidence = {"original": observer.digest(archive), "exposed": observer.digest(exposed),
                "globalized": symbols, "check": "all archive members' section contents, headers and relocations unchanged"}
    (out / "libdeflate-exposure.json").write_text(json.dumps(evidence, indent=2) + "\n")
    return evidence


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("clocks", type=Path)
    ap.add_argument("observation", type=Path)
    ap.add_argument("deps", type=Path)
    ap.add_argument("out", type=Path)
    ap.add_argument("--skip-proof", action="store_true", help="include explicitly UNVERIFIED native algorithm probes (AVX-512 VNNI required)")
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
    if a.skip_proof:
        src = deps / "isa-l"
        actual = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=src, text=True).strip()
        assert actual == ISAL_REV
        subprocess.run(["git", "diff", "--exit-code", "HEAD"], cwd=src, check=True, capture_output=True)
        build = out / "native" / "isa-l"
        shutil.copytree(src, build, ignore=shutil.ignore_patterns(".git"))
        with (out / "isa-l-build.log").open("w") as log:
            subprocess.run(["timeout", "-k", "5", "240", "make", "-f", "Makefile.unx", "-j4", "bin/isa-l.a"], cwd=build, stdout=log, stderr=subprocess.STDOUT, check=True, timeout=250)
        shutil.copyfile(build / "bin/isa-l.a", build / "libisal.a")
        shutil.copyfile(HERE / "probe.c", out / "probe.c")
        r["libdeflate_width_control"] = expose_libdeflate(out / "native/libdeflate/libdeflate.a", out, observer)
        r["experimental_probes"] = {"proof": "UNVERIFIED native C algorithm probes, not Ode implementations", "isa_l": ISAL_REV,
            "chunk": 16384, "widths": [32,64], "prefix_accumulators": [1,4],
            "reduce32": "additional 512/four-prefix variant: u32 A; u32 B at blocks <=5552, otherwise u64",
            "flags": "-O3 -DNDEBUG -fno-lto -mavx512bw -mavx512vl -mavx512vnni -mavx512dq; prefer vector width matching probe"}
    r["comparison"] = {"seed": 1, "sources": {name: rev for name, (rev, _) in DEPS.items()},
                       "build": "CMake Release, each project's default optimization flags, runtime dispatch enabled, static linking, no LTO"}
    r["benchmark_files"] = {name: observer.digest(HERE / name) for name in ["bench.rs", "bench_build.rs", "prepare_bench.py"] + (["probe.c"] if a.skip_proof else [])}
    (out / "report.json").write_text(json.dumps(r, indent=2) + "\n")
    for src, dst in [("bench.rs", "main.rs"), ("bench_build.rs", "build.rs")]:
        shutil.copyfile(HERE / src, out / dst)
    (out / "Cargo.toml").write_text(
        '[package]\nname = "ode-adler-observer"\nversion = "0.0.0"\nedition = "2021"\n'
        '[workspace]\n[features]\nprobe = []\n' + ('default = ["probe"]\n' if a.skip_proof else '') + '\n[[bin]]\nname = "ode-adler-observer"\npath = "main.rs"\n'
        '[dependencies]\nclocks = { path = ' + json.dumps(str(clocks / "clocks")) + ' }\n'
        '[profile.release]\ncodegen-units = 1\n')
    print(out / "Cargo.toml")


if __name__ == "__main__":
    main()
