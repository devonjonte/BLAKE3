#!/usr/bin/env python3
"""Whether short-message speed depends on where buffers and stacks happen to
sit, modulo the 4 KiB page (4 KiB aliasing), and whether that changed.

    python3 tools/offset_check.py [--exe BENCH] [--coarse] [--keep DIR]

Run from the fork's root with a bench-hashes checkout in `bench-hashes/` (or
pass --exe, a `bench-hashes build-against` executable). Linux with glibc:
it moves the duo-copy threads' stacks (glibc.rtld.optional_static_tls) and
the main thread's (environment size) through one whole page in 64-byte
steps (128 with --coarse), and measures a short-message cell set at each.

Why: a caller writes a short message and hashes it at once. When our call
chain's stack accesses share the message's low 12 address bits, the CPU
holds them behind the caller's stores (EPYC 9255: 1.05 to 1.5 ns/B for a
64-byte hash()). Which state a build lands in follows frame sizes, thread
count, environment and allocation history, none of which a relink changes,
so one offset can decide a comparison (bench-hashes #65).

How: a scan (one quick run per offset, reading the bench's printed report)
picks the worst offset for each cell; then `bench-hashes regress` compares
each cell's best scanned offset against its worst on fresh runs, judged as every
comparison is (clocks::summary). Selection and verdict use separate runs.

Verdicts:
- IMMUNE_CELLS are the cells our APIs keep free of the effect (the batch
  calls). Any one of them judged slower at some offset: exit 1.
- CONTROL_CELLS are known to be sensitive today (hash() of 64 bytes, a
  buffer lent or owned). If
  none is judged slower, the check lost its sight of the effect: exit 3.
  A change that makes them immune moves them to IMMUNE_CELLS with it.
- Exit 0 otherwise; 2 when regress gave no verdict (a busy machine).
"""
import argparse
import os
import pathlib
import re
import shutil
import statistics
import subprocess
import sys
import tempfile

CONTENDER = 'blake3-servil-st'
POINTS = ['lent 64 B', 'lent 256 B', 'continuous 64 B', 'continuous 256 B',
          'lent batch 16', 'lent batch 64', 'continuous batch 16', 'continuous batch 64']
# Batches of 64 messages: written long enough before the call. Batches of 16
# showed +6-8% at one offset on the EPYC, so they are on neither list.
IMMUNE_CELLS = [f'{CONTENDER}|{s}|{u}|64' for s in ('solo', 'shared')
                for u in ('LentBatches', 'ContinuousBatches')]
CONTROL_CELLS = [f'{CONTENDER}|{s}|{u}|64 B' for s in ('solo', 'shared')
                 for u in ('LentMessages', 'ContinuousMessages')]
PAGE = 4096
DEFAULT_TLS = 512
# Screening: a cell whose worst scanned run is this far above its median
# gets a confirmation. Confirmation alone decides.
SCREEN = 1.10
MAX_CONFIRMATIONS = 8


def offsets(step):
    """(name, environment additions) for each offset, the default first."""
    yield 'default', {}
    for k in range(1, PAGE // step):
        yield f'thread-stack+{k * step}', {'GLIBC_TUNABLES': f'glibc.rtld.optional_static_tls={DEFAULT_TLS + k * step}'}
    for k in range(1, PAGE // step):
        yield f'main-stack+{k * step}', {'OFFSET_CHECK_PAD': 'x' * (k * step)}


def run_env(extra):
    env = {'PATH': os.environ['PATH'], 'HOME': os.environ.get('HOME', '/')}
    env.update(extra)
    return env


def parse_report(text):
    """{(scenario, table title, size label): mean} from the printed report."""
    cells, scenario, table, header = {}, None, None, False
    for line in text.splitlines():
        if line.startswith('SOLO'):
            scenario = 'solo'
        elif line.startswith('SHARED'):
            scenario = 'shared'
        elif re.match(r'^  \S.*\((ns|us)/', line):
            table, header = line.strip(), False
        elif re.match(r'^  (size|messages)\s', line):
            header = True
        elif header and scenario and table:
            m = re.match(r'^\s+(\d+(?: [KMG]?i?B)?)\s+([\d.]+)\s*$', line)
            if m:
                cells[(scenario, table, m.group(1))] = float(m.group(2))
    return cells


def scan(exe, step, work):
    results = {}
    for name, extra in offsets(step):
        out = work / 'scan' / name
        out.mkdir(parents=True)
        subprocess.run([exe, '--contenders', CONTENDER, '--points', ','.join(POINTS),
                        '--for-regression-check', '--rounds', '24'],
                       cwd=out, env=run_env(extra), check=True,
                       stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
        report = next(out.glob('benchmark-results/*/bench-hashes.result.txt'))
        results[name] = parse_report(report.read_text())
        print(f'scan {name}: {len(results[name])} cells', file=sys.stderr, flush=True)
    return results


def pick(results):
    """(slow, fast) offset pairs to confirm: for each screened cell, its
    worst and best scanned offsets, most-affected first. The default offset
    has no special role: a build may sit in the slow state by default."""
    cells = set().union(*(r.keys() for r in results.values()))
    picks = {}
    for cell in cells:
        runs = {name: r[cell] for name, r in results.items() if cell in r}
        median = statistics.median(runs.values())
        worst, best = max(runs, key=runs.get), min(runs, key=runs.get)
        ratio = runs[worst] / median
        if ratio >= SCREEN and picks.get(worst, (0,))[0] < ratio:
            picks[worst] = (ratio, best)
    order = sorted(picks, key=lambda w: picks[w][0], reverse=True)[:MAX_CONFIRMATIONS]
    return [(w, picks[w][1]) for w in order], len(cells)


def wrapper(path, exe, extra):
    lines = ['#!/bin/sh', 'exec env -i ' + ' '.join(f"'{k}={v}'" for k, v in run_env(extra).items()) + f" '{exe}' \"$@\""]
    path.write_text('\n'.join(lines) + '\n')
    path.chmod(0o755)
    return str(path)


def confirm(exe, slow, fast, extras, work):
    """regress: the fast offset (old side) against the slow one (new)."""
    out = work / 'confirm' / slow
    out.mkdir(parents=True)
    old = [wrapper(out / f'fast-{i}', exe, extras[fast]) for i in range(4)]
    new = [wrapper(out / f'slow-{i}', exe, extras[slow]) for i in range(4)]
    done = subprocess.run([exe, 'regress', '--contenders', CONTENDER, '--points', ','.join(POINTS),
                           '--pairs', '4', '--keep', str(out / 'samples'), *old, '--', *new],
                          cwd=out, capture_output=True, text=True)
    (out / 'regress.out').write_text(done.stdout)
    (out / 'regress.err').write_text(done.stderr)
    slower = set(re.findall(r'^\s+SLOWER (\S+\|\S+\|\S+\|.+?):', done.stdout, re.M))
    return done.returncode, slower


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument('--exe', help='a bench-hashes build-against executable (default: build one)')
    parser.add_argument('--coarse', action='store_true', help='128-byte steps: half the runs')
    parser.add_argument('--keep', help='keep the scan and confirmation runs here')
    args = parser.parse_args()
    if not (sys.platform.startswith('linux') and os.confstr('CS_GNU_LIBC_VERSION')):
        sys.exit('offset_check: Linux with glibc only (it moves thread stacks with a glibc tunable)')
    exe = args.exe
    if exe is None:
        exe = subprocess.run(['cargo', 'run', '--quiet', '--release', '--', 'build-against', '..'],
                             cwd='bench-hashes', check=True, capture_output=True, text=True).stdout.strip()
    exe = str(pathlib.Path(exe).resolve())
    work = pathlib.Path(args.keep) if args.keep else pathlib.Path(tempfile.mkdtemp(prefix='offset-check-'))
    work.mkdir(parents=True, exist_ok=True)
    results = scan(exe, 128 if args.coarse else 64, work)
    picks, ncells = pick(results)
    print(f'scanned {len(results)} offsets x {ncells} cells; confirming {len(picks)}: '
          + (', '.join(f'{s} against {f}' for s, f in picks) or 'none'))
    extras = dict(offsets(128 if args.coarse else 64))
    sensitive, no_verdict = {}, False
    for slow, fast in picks:
        code, slower = confirm(exe, slow, fast, extras, work)
        no_verdict |= code == 2
        for cell in slower:
            sensitive.setdefault(cell, []).append(f'{slow} vs {fast}')
        print(f'confirm {slow} against {fast}: regress exit {code}; slower: {", ".join(sorted(slower)) or "none"}')
    broken = [c for c in IMMUNE_CELLS if c in sensitive]
    seen = [c for c in CONTROL_CELLS if c in sensitive]
    for cell, names in sorted(sensitive.items()):
        print(f'offset-sensitive: {cell} (slower at {", ".join(names)})')
    if not args.keep:
        shutil.rmtree(work)
    if broken:
        print(f'FAIL: cells our APIs keep immune turned offset-sensitive: {", ".join(broken)}')
        return 1
    if no_verdict and not seen:
        print('no verdict: a confirmation found the machine busy')
        return 2
    if not seen:
        print('FAIL: no control cell was judged sensitive: the check cannot see the effect here')
        return 3
    print(f'ok: immune cells stay immune; the check still sees the effect ({", ".join(seen)})')
    return 0


if __name__ == '__main__':
    sys.exit(main())
