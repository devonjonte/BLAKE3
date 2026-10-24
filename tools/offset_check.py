#!/usr/bin/env python3
"""Whether short-message speed depends on where buffers and stacks happen to
sit, modulo the 4 KiB page (4 KiB aliasing), and whether that changed.

    python3 tools/offset_check.py [--exe BENCH] [--step BYTES] [--keep DIR]
    python3 tools/offset_check.py --axis core [--exe BENCH] [--keep DIR]

With --axis core, the place a cell runs is each CPU in turn, pinned (Linux):
the cells bench-hashes #69 found to follow the physical core, solo, cores of
one kind compared (a hybrid's P and E cores apart), reported as
core-sensitive where the slowest core is confirmed slower than the fastest.

Run from the fork's root with a bench-hashes checkout in `bench-hashes/` (or
pass --exe, a `bench-hashes build-against` executable). Linux with glibc:
it moves the duo-copy threads' stacks (glibc.rtld.optional_static_tls)
through one whole page in 16-byte steps, the stack's own alignment
(--step for others), and measures a short-message cell set at each (the
main thread's stack: see offsets()).

Why: a caller writes a short message and hashes it at once. When our call
chain's stack accesses share the message's low 12 address bits, the CPU
holds them behind the caller's stores (EPYC 9255: 1.05 to 1.5 ns/B for a
64-byte hash()). Which state a build lands in follows frame sizes, thread
count, environment and allocation history, none of which a relink changes,
so one offset can decide a comparison (bench-hashes #65).

How: a scan (one quick run per offset, reading the bench's printed report),
then a rescan of each cell's few worst offsets, twice more: a slow state
stays slow when measured again, a stray reading does not, so a candidate's
score is the lowest of its three readings. Each cell's best-scoring
candidate is then compared against its best scanned offset by `bench-hashes
regress` on fresh runs, judged as every comparison is (clocks::summary).
Selection and verdict use separate runs; no threshold stands between a
small effect and its confirmation (the i7-12700K's is +9-11% in a window
48 bytes wide, which steps of 64 and a 10% screen both missed).

Verdicts:
- IMMUNE_CELLS are the cells our APIs keep free of the effect: our hash()
  of 64 bytes, a buffer lent or owned, since the x86-64 chunk-root kernel
  (#141). Any one of them judged slower at some offset: exit 1.
- CONTROL_CELLS are known to be sensitive: the upstream blake3 crate's
  hash() of 64 bytes, whose chunk path keeps its state on the stack as ours
  did. If none is judged slower, the check lost its sight of the effect:
  exit 3.
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
# The control contender: the upstream crate, whose 64-byte hash() still
# reads stack memory the caller's stores can hold back.
CONTROL = 'blake3-official'
POINTS = ['lent 64 B', 'lent 256 B', 'continuous 64 B', 'continuous 256 B',
          'lent batch 16', 'lent batch 64', 'continuous batch 16', 'continuous batch 64']
# Our 64-byte hash() is immune since the chunk-root kernel (#141). Batches
# are not: they were thought so, from scans in 64-byte steps; at 16-byte
# steps the EPYC 9255 shows 64-message batches +3-4% and 16-message +4-7%
# at a few offsets, every run (Sam Shackleton, #65, October 24), while the
# i7-12700K shows none. They are measured and reported with the rest. A
# change that makes a cell immune lists it here, and the check then fails
# if it turns sensitive again.
IMMUNE_CELLS = [f'{CONTENDER}|{s}|{u}|64 B' for s in ('solo', 'shared')
                for u in ('LentMessages', 'ContinuousMessages')]
CONTROL_CELLS = [f'{CONTROL}|{s}|{u}|64 B' for s in ('solo', 'shared')
                 for u in ('LentMessages', 'ContinuousMessages')]
PAGE = 4096
DEFAULT_TLS = 512
# Each cell's worst scanned offsets rescanned, and how many times. A single
# quick reading strays as high as a slow state reads (on the i7-12700K the
# window's 0.80 ns/B ranked anywhere from 1st to 10th among 256 offsets,
# under readings of 0.83-0.86 that read 0.73 again when rescanned), so ten
# a cell; a rescan run takes a fraction of a second.
CANDIDATES = 10
RESCANS = 2
MAX_CONFIRMATIONS = 8
# Pairs per confirmation. regress judges every cell of the set at once
# (Benjamini-Hochberg over 16 cells), and four pairs cannot get a cell
# below its bar: on the i7-12700K the slow offset ran +8% to +20% in every
# one of four pairs and was judged level. Eight can.
PAIRS = 8


def offsets(step):
    """(name, environment additions) for each offset, the default first.

    The duo threads' stacks only. The main thread's stack also moves with
    the environment's size, but its top holds the command line as well,
    and `regress` runs the bench with other arguments than the scan, so a
    main-stack offset found in the scan lands elsewhere in its
    confirmation: on the i7-12700K one read 1.38 times the median in all
    three scans and level under regress. Until a confirmation can hold the
    main stack where the scan had it, solo cells are not covered."""
    yield 'default', {}
    for k in range(1, PAGE // step):
        yield f'thread-stack+{k * step}', {'GLIBC_TUNABLES': f'glibc.rtld.optional_static_tls={DEFAULT_TLS + k * step}'}


# The core axis (--axis core): the cells bench-hashes #69 found to follow
# the physical core on the EPYC 9255 (odd cores up to 1.4x slower, same
# clock): batches of 64 and 256 messages and one message of 64 KiB, after
# other work, solo (pinned to one CPU, a shared cell's two copies would
# share it).
CORE_POINTS = ['64', '256', '64 KiB']


def cpu_kinds():
    """{cpu: kind} for the CPUs this process may use: a hybrid's core types
    from Linux's perf devices (cpu_core, cpu_atom), else one kind. Cores of
    different kinds differ by design (an E core is slower), so the core
    axis compares cores of one kind only."""
    allowed = sorted(os.sched_getaffinity(0))
    kinds = {}
    for kind in ('cpu_core', 'cpu_atom'):
        path = pathlib.Path(f'/sys/bus/event_source/devices/{kind}/cpus')
        if path.exists():
            for part in path.read_text().strip().split(','):
                lo, _, hi = part.partition('-')
                for cpu in range(int(lo), int(hi or lo) + 1):
                    kinds[cpu] = kind
    return {cpu: kinds.get(cpu, 'cpu') for cpu in allowed}


def cores():
    """The core axis's places: (name, (environment, cpu)) for each CPU."""
    return [(f'cpu{cpu}', ({}, cpu)) for cpu in cpu_kinds()]


def pinned(cpu):
    """A command's prefix that pins it to `cpu` (none for no pin)."""
    return [] if cpu is None else ['taskset', '-c', str(cpu)]


def run_env(extra):
    env = {'PATH': os.environ['PATH'], 'HOME': os.environ.get('HOME', '/')}
    env.update(extra)
    return env


def parse_report(text):
    """{(column, scenario, table title, size label): mean} from the printed
    report; one column per contender, headed by its display name."""
    cells, scenario, table, columns = {}, None, None, None
    for line in text.splitlines():
        if line.startswith('SOLO'):
            scenario = 'solo'
        elif line.startswith('SHARED'):
            scenario = 'shared'
        elif re.match(r'^  \S.*\((ns|us)/', line):
            table, columns = line.strip(), None
        elif re.match(r'^  (size|messages)\s', line):
            columns = re.split(r'\s{2,}', line.strip())[1:]
        elif columns and scenario and table:
            m = re.match(r'^\s+(\d+(?: [KMG]?i?B)?)((?:\s+[\d.]+)+)\s*$', line)
            if m:
                for column, value in zip(columns, m.group(2).split()):
                    cells[(column, scenario, table, m.group(1))] = float(value)
    return cells


def scan(exe, named, work, points, label='scan'):
    """{place name: {cell: mean}}, one quick run per (name, (environment,
    cpu)): the environment moves the stacks, the cpu (if any) pins it."""
    results = {}
    for name, (extra, cpu) in named:
        out = work / label / name
        out.mkdir(parents=True)
        subprocess.run([*pinned(cpu), exe, '--contenders', f'{CONTENDER},{CONTROL}', '--points', ','.join(points),
                        '--for-regression-check', '--rounds', '24'],
                       cwd=out, env=run_env(extra), check=True,
                       stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
        report = next(out.glob('benchmark-results/*/bench-hashes.result.txt'))
        results[name] = parse_report(report.read_text())
        print(f'{label} {name}: {len(results[name])} cells', file=sys.stderr, flush=True)
    return results


def candidates(results):
    """The offsets to rescan: each cell's CANDIDATES worst."""
    cells = set().union(*(r.keys() for r in results.values()))
    chosen = set()
    for cell in cells:
        runs = {name: r[cell] for name, r in results.items() if cell in r}
        chosen.update(sorted(runs, key=runs.get, reverse=True)[:CANDIDATES])
    return chosen


def pick(results, rescans, kind=lambda name: None, cell_ok=lambda cell: True):
    """(slow, fast) place pairs to confirm, most-affected first: for each
    cell, and among places of one kind (the core axis: a core type), the
    rescanned place whose lowest reading (scan and rescans) is highest,
    against the cell's fastest scanned place of that kind. The default
    place has no special role: a build may sit in the slow state there."""
    cells = {c for c in set().union(*(r.keys() for r in results.values())) if cell_ok(c)}
    picks = {}
    for cell in cells:
        for k in {kind(name) for name in results}:
            runs = {name: r[cell] for name, r in results.items() if cell in r and kind(name) == k}
            if len(runs) < 2:
                continue
            median = statistics.median(runs.values())
            lowest = {name: min([runs[name]] + [r[name][cell] for r in rescans if cell in r.get(name, {})])
                      for name in rescans[0] if name in runs}
            if not lowest:
                continue
            worst, best = max(lowest, key=lowest.get), min(runs, key=runs.get)
            ratio = lowest[worst] / median
            if picks.get(worst, (0,))[0] < ratio:
                picks[worst] = (ratio, best)
    order = sorted(picks, key=lambda w: picks[w][0], reverse=True)[:MAX_CONFIRMATIONS]
    return [(w, picks[w][1], picks[w][0]) for w in order], len(cells)


def wrapper(path, exe, place):
    extra, cpu = place
    lines = ['#!/bin/sh', 'exec ' + ''.join(f"{w} " for w in pinned(cpu)) + 'env -i ' + ' '.join(f"'{k}={v}'" for k, v in run_env(extra).items()) + f" '{exe}' \"$@\""]
    path.write_text('\n'.join(lines) + '\n')
    path.chmod(0o755)
    return str(path)


def confirm(exe, slow, fast, places, work, points):
    """regress: the fast place (old side) against the slow one (new)."""
    out = work / 'confirm' / slow
    out.mkdir(parents=True)
    old = [wrapper(out / f'fast-{i}', exe, places[fast]) for i in range(PAIRS)]
    new = [wrapper(out / f'slow-{i}', exe, places[slow]) for i in range(PAIRS)]
    done = subprocess.run([exe, 'regress', '--contenders', f'{CONTENDER},{CONTROL}', '--points', ','.join(points),
                           '--pairs', str(PAIRS), '--keep', str(out / 'samples'), *old, '--', *new],
                          cwd=out, capture_output=True, text=True)
    (out / 'regress.out').write_text(done.stdout)
    (out / 'regress.err').write_text(done.stderr)
    slower = set(re.findall(r'^\s+SLOWER (\S+\|\S+\|\S+\|.+?):', done.stdout, re.M))
    return done.returncode, slower


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument('--exe', help='a bench-hashes build-against executable (default: build one)')
    parser.add_argument('--step', type=int, default=16, help='bytes between offsets (default 16, the stack alignment)')
    parser.add_argument('--keep', help='keep the scan and confirmation runs here')
    parser.add_argument('--axis', choices=['stack', 'core'], default='stack',
                        help="stack: the duo threads' stack through a page (default); core: each CPU in turn, pinned (bench-hashes #69)")
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
    if args.axis == 'core':
        return core_axis(exe, work, args.keep)
    places = {name: (extra, None) for name, extra in offsets(args.step)}
    results = scan(exe, places.items(), work, POINTS)
    again = sorted(candidates(results))
    rescans = [scan(exe, [(name, places[name]) for name in again], work, POINTS, f'rescan{i + 1}') for i in range(RESCANS)]
    picks, ncells = pick(results, rescans)
    print(f'scanned {len(results)} offsets x {ncells} cells, rescanned {len(again)} twice; confirming {len(picks)}: '
          + (', '.join(f'{s} ({r:.2f}x the median at its lowest) against {f}' for s, f, r in picks) or 'none'))
    sensitive, no_verdict = {}, False
    for slow, fast, _ in picks:
        code, slower = confirm(exe, slow, fast, places, work, POINTS)
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


def core_axis(exe, work, keep):
    """The core axis: each CPU this process may use in turn, solo cells
    only, cores of one kind compared; each cell whose slowest core is
    confirmed slower than its fastest is core-sensitive. A measurement:
    exit 0 whatever it finds, 2 when a confirmation found the machine
    busy."""
    kinds = cpu_kinds()
    places = dict(cores())
    kind = lambda name: kinds[int(name[3:])]
    results = scan(exe, places.items(), work, CORE_POINTS)
    again = sorted(candidates(results))
    rescans = [scan(exe, [(name, places[name]) for name in again], work, CORE_POINTS, f'rescan{i + 1}') for i in range(RESCANS)]
    solo = lambda cell: cell[1] == 'solo'
    picks, ncells = pick(results, rescans, kind, solo)
    print(f'scanned {len(results)} CPUs ({", ".join(sorted(set(kinds.values())))}) x {ncells} solo cells, rescanned {len(again)} twice; confirming {len(picks)}: '
          + (', '.join(f'{s} ({r:.2f}x its kind\'s median at its lowest) against {f}' for s, f, r in picks) or 'none'))
    sensitive, no_verdict = {}, False
    for slow, fast, _ in picks:
        code, slower = confirm(exe, slow, fast, places, work, CORE_POINTS)
        no_verdict |= code == 2
        for cell in (c for c in slower if c.split('|')[1] == 'solo'):
            sensitive.setdefault(cell, []).append(f'{slow} vs {fast}')
        print(f'confirm {slow} against {fast}: regress exit {code}; slower: {", ".join(sorted(slower)) or "none"}')
    for cell, names in sorted(sensitive.items()):
        print(f'core-sensitive: {cell} (slower on {", ".join(names)})')
    if not keep:
        shutil.rmtree(work)
    if no_verdict and not sensitive:
        print('no verdict: a confirmation found the machine busy')
        return 2
    print(f'{len(sensitive)} cells core-sensitive' if sensitive else 'no cell core-sensitive: every core of a kind ran them alike')
    return 0


if __name__ == '__main__':
    sys.exit(main())
