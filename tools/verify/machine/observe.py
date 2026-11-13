#!/usr/bin/env python3
"""Observe one Ode function's compiled structure; no timing or proof verdict.

    python3 observe.py SOURCE.ode FUNCTION OUTPUT_DIRECTORY

Uses Ode's own parser and Lean assembly/layout printers, then the assembler and
LLVM disassembler. OUTPUT_DIRECTORY must be new. All subprocesses have deadlines.
The exact isolated function's text is fingerprinted; linked addresses, callees'
costs, dynamic instruction counts and elapsed time are separate observations.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

HERE = Path(__file__).resolve().parent


def run(args, *, cwd=None, timeout=120):
    return subprocess.run([str(a) for a in args], cwd=cwd, check=True,
                          text=True, capture_output=True, timeout=timeout).stdout


def digest(path):
    return {"sha256": hashlib.sha256(path.read_bytes()).hexdigest(),
            "blake3": run(["b3sum", "--no-names", path]).strip()}


def instructions(listing):
    """LLVM's no-raw-bytes form: exactly one instruction per address line."""
    return [m.group(1).strip() for line in listing.splitlines()
            if (m := re.fullmatch(r"\s*[0-9a-fA-F]+:\s+(.+)", line))]


def observe(source, function, out):
    source, out = source.resolve(), out.resolve()
    if not re.fullmatch(r"[A-Za-z_][A-Za-z_0-9]*", function):
        raise ValueError("FUNCTION is an Ode identifier")
    out.mkdir(parents=True, exist_ok=False)
    lang = HERE / "lang"
    objdump = os.environ.get("OBJDUMP", "llvm-objdump-21")
    cc = os.environ.get("CC", "cc")
    objcopy = os.environ.get("OBJCOPY", "objcopy")
    # A snapshot prevents the report from accidentally naming edited source.
    snapshot = out / "source.ode"
    snapshot.write_bytes(source.read_bytes())
    ir = out / "Observed.lean"
    run(["python3", lang / "odec.py", snapshot, ir], cwd=lang)
    run(["lake", "build", "Lang"], cwd=lang)
    asm = run(["lake", "env", "lean", "--run", ir, "asm", "b3l_", "only", function], cwd=lang)
    # The existing printer otherwise emits an empty object for a misspelled name.
    if f"\nb3l_{function}:\n" not in asm:
        raise ValueError(f"no function named {function}")
    layout = run(["lake", "env", "lean", "--run", ir, "layout", function], cwd=lang)
    (out / "function.S").write_text(asm)
    (out / "layout.txt").write_text(layout)
    run([cc, "-c", out / "function.S", "-o", out / "function.o"])
    listing = run([objdump, "-d", "--no-show-raw-insn", "--x86-asm-syntax=intel", out / "function.o"])
    (out / "disassembly.txt").write_text(listing)
    run([objcopy, "--dump-section", f".text={out / 'text.bin'}", out / "function.o"])
    ins = instructions(listing)
    if not ins:
        raise ValueError("the disassembler found no instructions")
    def field(name):
        return next(line[len(name) + 1:] for line in layout.splitlines() if line.startswith(name + " "))
    repo = run(["git", "rev-parse", "--show-toplevel"], cwd=HERE).strip()
    report = {
        "format": "ode-observe-v1", "function": function, "target": "x86_64-linux-gnu",
        "proof": "not checked by this tool",
        "source": digest(snapshot),
        "compiler": {
            "commit": run(["git", "rev-parse", "HEAD"], cwd=HERE).strip(),
            "files": {str(p.relative_to(Path(repo))): digest(p) for p in
                      [Path(__file__).resolve(), lang / "odec.py", lang / "Lang.lean"]},
            "lean": run(["lake", "env", "lean", "--version"], cwd=lang).strip(),
            "assembler": run([cc, "--version"]).splitlines()[0],
            "disassembler": run([objdump, "--version"]).splitlines()[0],
        },
        "text": {"bytes": (out / "text.bin").stat().st_size, **digest(out / "text.bin")},
        "static_instructions": len(ins),
        "static_calls": sum(i.split()[0].startswith("call") for i in ins),
        "static_conditional_branches": sum(i.split()[0].startswith("j") and i.split()[0] != "jmp" for i in ins),
        "saved_registers": field("saved").split(),
        "frame_reservation_bytes": int(field("frame")),
        "layout": layout.splitlines(),
        "scope": "isolated .text; includes prologue and epilogue; excludes callees and linked placement; static counts are not execution costs",
    }
    (out / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    return report


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("source", type=Path)
    ap.add_argument("function")
    ap.add_argument("out", type=Path)
    args = ap.parse_args()
    if os.uname().sysname != "Linux" or os.uname().machine != "x86_64":
        ap.error("this first observer targets x86-64 Linux")
    try:
        r = observe(args.source, args.function, args.out)
    except (ValueError, subprocess.CalledProcessError, subprocess.TimeoutExpired) as e:
        if isinstance(e, subprocess.CalledProcessError):
            ap.exit(1, e.stdout + e.stderr)
        ap.exit(1, str(e) + "\n")
    print(f"{r['function']}: {r['text']['bytes']} bytes, {r['static_instructions']} static instructions, "
          f"{r['static_calls']} call sites; frame reservation {r['frame_reservation_bytes']} bytes, "
          f"{len(r['saved_registers'])} saved registers")
    print(f"Report: {args.out / 'report.json'}; proof status: {r['proof']}")


if __name__ == "__main__":
    main()
