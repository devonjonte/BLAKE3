#!/usr/bin/env python3
"""Enforce single-frame release stack budgets via ELF `.stack_sizes`.

Builds `b3sum` (which links `blake3_servil_core`, `blake3_servil`, and `b3sums`)
with `RUSTC_BOOTSTRAP=1 RUSTFLAGS="-Z emit-stack-sizes"` into a dedicated target
subdirectory so it never invalidates the main Cargo cache, then parses
`llvm-readobj --stack-sizes` and enforces the caps approved for #499:

- `blake3_servil_core` / `b3sums`: <= 128 KiB (131,072 bytes)
- `blake3_servil_core` `Hasher` methods: <= 32 KiB (32,768 bytes)
- `blake3_servil` (`threads/`): <= 16 KiB (16,384 bytes)
"""

from __future__ import annotations

import os
import re
import shutil
import subprocess
import sys
from pathlib import Path

CAP_CORE_B3SUM = 128 * 1024  # 131,072 B
CAP_HASHER = 32 * 1024       #  32,768 B
CAP_THREADS = 16 * 1024      #  16,384 B

# Match both legacy (`_ZN...18blake3_servil_core...`) and v0 (`_R...18blake3_servil_core...`)
# Rust mangled names as well as already-demangled names.
_SIZE_RE = re.compile(r"Size:\s*(0x[0-9a-fA-F]+|\d+)")
_FUNCS_RE = re.compile(r"Functions:\s*\[([^\]]*)\]")


def classify_symbol(sym: str) -> tuple[str, int] | None:
    """Return `(bucket_name, cap_bytes)` for our shipped crates, or None."""
    if "blake3_servil_core" in sym:
        if ("Hasher" in sym or "6Hasher" in sym) and "6update" not in sym and "::update" not in sym:
            return ("core::Hasher", CAP_HASHER)
        return ("core", CAP_CORE_B3SUM)
    if "blake3_servil" in sym:
        return ("threads", CAP_THREADS)
    if "b3sums" in sym or "b3sum" in sym:
        return ("b3sum", CAP_CORE_B3SUM)
    return None


def parse_llvm_readobj_stack_sizes(text: str) -> list[tuple[int, str]]:
    """Parse `llvm-readobj --stack-sizes` output into `(size_bytes, symbol)` pairs."""
    entries: list[tuple[int, str]] = []
    cur_size: int | None = None
    for line in text.splitlines():
        m_fn = _FUNCS_RE.search(line)
        if m_fn:
            funcs = [f.strip() for f in m_fn.group(1).split(",") if f.strip()]
            if cur_size is not None:
                for fn in funcs:
                    entries.append((cur_size, fn))
                cur_size = None
            else:
                # Some llvm-readobj versions print Functions before Size.
                pending_funcs = funcs
                continue
        m_sz = _SIZE_RE.search(line)
        if m_sz:
            raw = m_sz.group(1)
            sz = int(raw, 16) if raw.startswith("0x") else int(raw)
            if "pending_funcs" in locals() and pending_funcs:
                for fn in pending_funcs:
                    entries.append((sz, fn))
                pending_funcs = []
                cur_size = None
            else:
                cur_size = sz
    return entries


def check_entries(entries: list[tuple[int, str]]) -> tuple[dict[str, tuple[int, str]], list[str]]:
    """Return `(max_by_bucket, violation_messages)`."""
    max_by_bucket: dict[str, tuple[int, str]] = {}
    violations: list[str] = []
    for size, sym in entries:
        cls = classify_symbol(sym)
        if cls is None:
            continue
        bucket, cap = cls
        prev = max_by_bucket.get(bucket)
        if prev is None or size > prev[0]:
            max_by_bucket[bucket] = (size, sym)
        if size > cap:
            violations.append(f"{bucket}: {size} B > {cap} B cap in {sym}")
    return max_by_bucket, violations


def main() -> int:
    readobj = shutil.which("llvm-readobj")
    if not readobj:
        print("stack_budget: llvm-readobj not found in PATH", file=sys.stderr)
        return 1

    repo = Path(__file__).resolve().parent.parent
    base_target = Path(os.environ.get("CARGO_TARGET_DIR", str(repo / "target")))
    stack_target = base_target / "stack-budget"

    env = os.environ.copy()
    env["RUSTC_BOOTSTRAP"] = "1"
    existing_flags = env.get("RUSTFLAGS", "").strip()
    env["RUSTFLAGS"] = f"{existing_flags} -Z emit-stack-sizes".strip()
    env["CARGO_TARGET_DIR"] = str(stack_target)

    subprocess.run(
        [
            "cargo",
            "build",
            "--quiet",
            "--release",
            "--manifest-path",
            str(repo / "b3sum" / "Cargo.toml"),
            "--bin",
            "b3sum",
        ],
        cwd=repo,
        env=env,
        check=True,
    )

    binary = stack_target / "release" / "b3sum"
    proc = subprocess.run(
        [readobj, "--stack-sizes", str(binary)],
        capture_output=True,
        text=True,
        check=True,
    )
    entries = parse_llvm_readobj_stack_sizes(proc.stdout)
    if not entries:
        print("stack_budget: no .stack_sizes entries found in binary", file=sys.stderr)
        return 1

    max_by_bucket, violations = check_entries(entries)
    if not max_by_bucket:
        print("stack_budget: no shipped-crate symbols found in .stack_sizes", file=sys.stderr)
        return 1

    summary = ", ".join(
        f"{bucket}={sz}B" for bucket, (sz, _) in sorted(max_by_bucket.items())
    )
    if violations:
        print(f"stack_budget: FAILED ({len(violations)} violation(s); max: {summary})", file=sys.stderr)
        for v in violations:
            print(f"  {v}", file=sys.stderr)
        return 1

    print(f"stack_budget: OK ({len(entries)} symbols checked; max: {summary})")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
