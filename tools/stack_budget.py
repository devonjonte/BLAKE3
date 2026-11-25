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

# Match Entry blocks and anchored Size/Functions lines inside `llvm-readobj --stack-sizes`
# so headers like `AddressSize: 64bit` outside `Entry { ... }` are never parsed as stack sizes.
_ENTRY_OPEN_RE = re.compile(r"^\s*Entry\s*\{\s*$")
_ENTRY_CLOSE_RE = re.compile(r"^\s*\}\s*$")
_SIZE_RE = re.compile(r"^\s*Size:\s*(0x[0-9a-fA-F]+|\d+)\s*$")
_FUNCS_RE = re.compile(r"^\s*Functions:\s*\[([^\]]*)\]\s*$")

# Match owning-crate tokens in v0 (`_R...18blake3_servil_core...`), legacy (`_ZN18blake3_servil_core...`),
# and demangled (`blake3_servil_core::...`) symbols; the earliest match identifies the defining crate
# rather than a type argument from another crate (e.g. `Pipeline<..., blake3_servil_core::block::Batch>`).
_CRATE_RE = re.compile(
    r"(?:(?<!\d)18blake3_servil_core(?![A-Za-z_])|\bblake3_servil_core::)"
    r"|(?:(?<!\d)13blake3_servil(?![A-Za-z_])|\bblake3_servil::)"
    r"|(?:(?<!\d)6b3sums(?![A-Za-z_])|(?<!\d)5b3sum(?![A-Za-z_])|\bb3sums?::)"
)
_HASHER_RE = re.compile(r"(?:(?<!\d)6Hasher(?![A-Za-z_])|::Hasher::)")
_UPDATE_RE = re.compile(r"(?:(?<!\d)6update(?![A-Za-z_])|::update(?:_|\b))")


def classify_symbol(sym: str) -> tuple[str, int] | None:
    """Return `(bucket_name, cap_bytes)` for our shipped crates, or None."""
    m = _CRATE_RE.search(sym)
    if m is None:
        return None
    tok = m.group(0)
    if "blake3_servil_core" in tok:
        if _HASHER_RE.search(sym) and not _UPDATE_RE.search(sym):
            return ("core::Hasher", CAP_HASHER)
        return ("core", CAP_CORE_B3SUM)
    if "blake3_servil" in tok:
        return ("threads", CAP_THREADS)
    return ("b3sum", CAP_CORE_B3SUM)


def parse_llvm_readobj_stack_sizes(text: str) -> list[tuple[int, str]]:
    """Parse `llvm-readobj --stack-sizes` output into `(size_bytes, symbol)` pairs."""
    entries: list[tuple[int, str]] = []
    in_entry = False
    entry_size: int | None = None
    entry_funcs: list[str] = []
    for line in text.splitlines():
        if _ENTRY_OPEN_RE.match(line):
            in_entry = True
            entry_size = None
            entry_funcs = []
            continue
        if not in_entry:
            continue
        if _ENTRY_CLOSE_RE.match(line):
            if entry_size is not None:
                for fn in entry_funcs:
                    entries.append((entry_size, fn))
            in_entry = False
            entry_size = None
            entry_funcs = []
            continue
        m_fn = _FUNCS_RE.match(line)
        if m_fn:
            entry_funcs = [f.strip() for f in m_fn.group(1).split(",") if f.strip()]
            continue
        m_sz = _SIZE_RE.match(line)
        if m_sz:
            raw = m_sz.group(1)
            entry_size = int(raw, 16) if raw.startswith("0x") else int(raw)
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
            "--locked",
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
