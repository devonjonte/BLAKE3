"""The Python twin of the clocks crate's `speeds` module (clocks/src/speeds.rs):
the one way every tool summarises and compares a cell's samples, which may
run at two speeds. perf_regress, losses.py, ab.py, and every scratch probe
in Python import it; both implementations are held to the vectors in
clocks/speeds_vectors.txt (`pypy3 tools/speeds.py` checks them).

Samples enter as exact nanoseconds per unit (Fraction), then use the
same Q64.64 representation and half-up midpoint as Rust. The rule: sort; a cell
has two speeds when two neighbours in sorted order are GAP_PERMILLE of the
median or more apart, with MIN_SHARE_PERMILLE of the samples or more on
each side, and the slower side's median is RATIO_PERMILLE of the faster's
or more (rounded to permille, as reports print it); the widest such gap
splits them. Never compare two cells by a lone median or mean: compare
speed with speed and share with share (compare()).
"""
from fractions import Fraction
from pathlib import Path

GAP_PERMILLE = 40
MIN_SHARE_PERMILLE = 100
RATIO_PERMILLE = 1250


Q64 = 1 << 64


def fixed(value):
    """Rust's per_unit: nearest Q64.64, half up, as an exact Fraction."""
    value = Fraction(value)
    assert value >= 0, "a sample is non-negative"
    n, d = value.numerator, value.denominator
    return Fraction((n * Q64 * 2 + d) // (2 * d), Q64)


def median_of_sorted(v):
    assert v, "a median needs a sample"
    m = len(v) // 2
    return v[m] if len(v) % 2 else fixed((v[m - 1] + v[m]) / 2)


def ratio_permille(a, b):
    """a / b in permille, rounded half up."""
    assert b > 0
    return int(Fraction(a) * 1000 / Fraction(b) + Fraction(1, 2))


def split(v):
    """The index in sorted `v` of the first slow sample, or None for one speed."""
    v = [fixed(x) for x in v]
    n = len(v)
    assert n > 0, "a split needs a sample"
    median = median_of_sorted(v)
    min_side = max(1, -(-n * MIN_SHARE_PERMILLE // 1000))
    best = None
    for at in range(min_side, n - min_side + 1):
        if at in (0, n):
            continue
        gap = v[at] - v[at - 1]
        if gap * 1000 >= median * GAP_PERMILLE and (best is None or gap > best[1]):
            best = (at, gap)
    if best is None:
        return None
    at = best[0]
    fast, slow = median_of_sorted(v[:at]), median_of_sorted(v[at:])
    return at if ratio_permille(slow, fast) >= RATIO_PERMILLE else None


def speeds(values):
    """[(median, count)], faster first: one speed, or two."""
    v = sorted(fixed(x) for x in values)
    at = split(v)
    parts = [v] if at is None else [v[:at], v[at:]]
    return [(median_of_sorted(p), len(p)) for p in parts]


def slow_share_permille(s):
    total = sum(count for _, count in s)
    return 0 if len(s) < 2 else (s[1][1] * 1000 + total // 2) // total


def compare(old, new):
    """Speed with speed and share with share: a dict with each side's
    speeds, new/old of the fast and of the slow speeds' medians (permille;
    a side with one speed: that speed is both), and each side's slow share
    (permille)."""
    a, b = speeds(old), speeds(new)
    return {"old": a, "new": b,
            "fast_permille": ratio_permille(b[0][0], a[0][0]),
            "slow_permille": ratio_permille(b[-1][0], a[-1][0]),
            "old_slow_share_permille": slow_share_permille(a),
            "new_slow_share_permille": slow_share_permille(b),
            "two_speeds": len(a) > 1 or len(b) > 1}


def describe(s, fmt=lambda x: f"{float(x):.3g}"):
    """'0.21' or '0.21 (70%) | 0.50 (30%)': each speed's median and share."""
    if len(s) == 1:
        return fmt(s[0][0])
    total = sum(c for _, c in s)
    return " | ".join(f"{fmt(m)} ({(c * 100 + total // 2) // total}%)" for m, c in s)


def describe_comparison(c, fmt=lambda x: f"{float(x):.3g}"):
    """One line: old speeds -> new speeds, and the per-speed ratios."""
    text = f"{describe(c['old'], fmt)} -> {describe(c['new'], fmt)}"
    if c["two_speeds"]:
        text += (f"  [fast x{c['fast_permille'] / 1000:.2f}, slow x{c['slow_permille'] / 1000:.2f}, "
                 f"slow share {c['old_slow_share_permille'] // 10}% -> {c['new_slow_share_permille'] // 10}%]")
    else:
        text += f"  [x{c['fast_permille'] / 1000:.2f}]"
    return text


def check_vectors():
    path = Path(__file__).resolve().parents[1] / "clocks/speeds_vectors.txt"
    checked = 0
    for line in path.read_text().splitlines():
        if not line.strip() or line.startswith("#"):
            continue
        samples, expected = line.split(" -> ")
        v = sorted(Fraction(*map(int, s.strip().split("/"))) for s in samples.split(","))
        want = None if expected.strip() == "none" else int(expected)
        assert split(v) == want, f"{line}: split {split(v)}, expected {want}"
        checked += 1
    assert checked >= 8
    return checked


if __name__ == "__main__":
    print(f"speeds.py: {check_vectors()} vectors agree with the rule")
