"""hash_many for every input count, by induction over full-width passes.

Array bytes are independent at every input offset. The remainder is a
symbolic count below the SIMD width; the executor explores each tail path.
Base runs cover counts below one pass. The group invariant then proves
all larger counts whose input-region size fits in a 64-bit address.
"""
from z3 import (Array, BitVecSort, BitVec, BitVecVal, Select, ZeroExt, ULT, ULE, UGE,
                simplify, substitute, is_bv, Solver, unsat)
import aarch64 as arm
import induction as ind
import x86
from aarch64 import Ptr, Region, Unproved
from prove_hybrid import byte_symbols, same, table_cvs
import lean_spec as spec


def pass_head(setup, so, width):
    """The full-width loop's back edge: sub count,W; cmp count,W; jae."""
    code = setup.m.code
    symbols = x86.symbols(so)
    end = min((pc for name, pc in symbols.items()
               if name.startswith(('blake3_', '_blake3_')) and pc > setup.entry), default=x86.text_end(so))
    pcs = sorted(pc for pc in code if setup.entry <= pc < end)
    heads = []
    for i, pc in enumerate(pcs):
        mnem, ops, _ = code[pc]
        if i < 2 or mnem not in ('jae', 'jnc'):
            continue
        target = int(ops[0].split()[0], 16)
        sub, sops, _ = code[pcs[i - 2]]
        cmp, cops, _ = code[pcs[i - 1]]
        if (target < pc and sub == 'sub' and cmp == 'cmp' and sops == cops
                and x86.imm(sops[1]) == width):
            heads.append(target)
    if len(heads) != 1:
        raise Unproved(f'expected one full-width pass loop, found {list(map(hex, heads))}')
    return heads[0]


def counter_invariant(general, first, second, counter, k, width):
    """State counter-derived positions as f(counter + W*K).

The pair of arrivals must establish f(counter+W), including both halves'
carry, before the formula enters the invariant. The caller also checks
the complete invariant at K=0 and the executor checks its successor.
"""
    def advance(a, b):
        if not is_bv(a) or not is_bv(b):
            return None
        symbols = arm.term_symbols(a)
        if not symbols or not symbols <= {'counter'} or not arm.term_symbols(b) <= {'counter'}:
            return None
        next_value = substitute(a, (counter, counter + width))
        # This is a lemma for every counter, independent of any group or
        # remainder bounds. Keep their unrelated arithmetic out of it.
        solver = Solver()
        solver.add(b != next_value)
        if solver.check() != unsat:
            return None
        return substitute(a, (counter, counter + width * k))
    for r in first.x:
        value = advance(first.x[r], second.x[r])
        if value is not None:
            general.x[r] = value
    for r, lanes in first.v.items():
        for lane, a in enumerate(lanes):
            value = advance(a, second.v[r][lane])
            if value is not None:
                general.v[r][lane] = value
    for name, mem in general.mem.items():
        if name == 'out':
            continue
        r0, r1 = first.regions[name], second.regions[name]
        for off in sorted(o for o in mem if isinstance(o, int) and o % 8 == 0):
            a, b = ind.word(r0, off), ind.word(r1, off)
            value = advance(a, b)
            if value is not None:
                for j in range(8):
                    mem[off + j] = ('word', value, j)


def prove(so, isa, windows, blocks, increment):
    import prove_x86 as p
    assert 1 <= blocks <= 16, 'hash_many takes 1..16 full blocks per input'
    width = p.WIDTH[isa]
    group, rem, k = (BitVec(n, 64) for n in ('len_groups', 'len_rem', 'len_k'))
    count = group * width + rem
    # 64*blocks*count is the size of one abstract input region. No region
    # length or loop pointer wraps. The width and block count are powers
    # of two only where the assembly requires it; this bound uses division.
    bound = ((((1 << 64) - 1) // (64 * blocks)) - (width - 1)) // width
    data = Array('inputs', BitVecSort(64), BitVecSort(8))
    key = byte_symbols('key', 32)
    counter = BitVec('counter', 64)
    flags, start, end = p.u8('flags'), p.u8('start'), p.u8('end')

    def table_byte(offset):
        if isinstance(offset, int):
            return (Ptr('inputs', offset // 8 * 64 * blocks), offset % 8)
        j = ind.forced(arm._machine[0], arm.as_bv(offset) & 7)
        if j is None:
            raise Unproved('table read byte is unconstrained')
        entry = simplify((arm.as_bv(offset) - j) * (8 * blocks), som=True, bv_sort_ac=True)
        return (Ptr('inputs', entry), j)
    regions = {
        'inputs': Region('inputs', count * (64 * blocks), False, lambda o: Select(data, arm.as_bv(o))),
        'table': Region('table', count * 8, False, table_byte),
        'key': Region('key', 32, False, lambda o: key[o]),
        'out': Region('out', count * 32, True, None),
    }
    for name in ('inputs', 'table'):
        regions[name].symbolic_initial = True
    args = [Ptr('table', 0), count, BitVecVal(blocks, 64), Ptr('key', 0), counter,
            BitVecVal(int(increment), 64), ZeroExt(56, flags), ZeroExt(56, start), ZeroExt(56, end), Ptr('out', 0)]
    setup = p.Setup(so, f'blake3_hash_many_{isa}', regions, args, windows)
    machine = setup.m
    flag_words = [ZeroExt(24, f) for f in (flags | start | end, flags | start, flags | end, flags)] + [BitVecVal(64, 32)]
    p.d_row_facts(machine, counter, 2 * width if increment else 1, flag_words)
    machine.lengths = {'len_groups', 'len_rem', 'len_k', 'counter'}
    bounds = [ULT(rem, width), ULE(group, bound)]
    machine.assumptions = bounds
    head = pass_head(setup, so, width)

    def check_range(m, first, n):
        first = arm.as_bv(first)
        inputs = [[Select(data, simplify((first + lane) * (64 * blocks) + j, som=True, bv_sort_ac=True))
                   for j in range(64 * blocks)] for lane in range(n)]
        counters = [counter + first + lane if increment else counter for lane in range(n)]
        cvs = table_cvs(inputs, key, counters, flags, start, end, BitVecVal(64, 8), blocks)
        out, expected = m.regions['out'], set()
        for lane in range(n):
            offsets = [arm.key(32 * (first + lane) + j) for j in range(32)]
            expected.update(offsets)
            if any(o not in out.bytes for o in offsets):
                raise Unproved(f'output {lane} incomplete')
            got = spec.words([out.bytes[o] for o in offsets])
            for word in range(8):
                if not same(got[word], cvs[lane][word]):
                    raise Unproved(f'output {lane}, word {word}, differs')
        return expected

    def exactly(m, expected):
        actual = {o for o, value in m.regions['out'].bytes.items() if value is not None}
        if actual != expected:
            raise Unproved('writes outside its output range')

    def tail_count(m):
        n = ind.forced(m, rem)
        if n is None:
            raise Unproved('a tail path leaves its output count open')
        return n

    # Counts below one full pass, including zero. The induction's entry
    # covers one or more passes and every remainder.
    print('  base: no full pass, every remainder', flush=True)
    base = ind.snapshot(machine)
    base.assumptions += [group == 0]
    for m, how in ind.paths(base, setup.entry, set()):
        if how != 'return':
            raise Unproved('base case fails to return')
        import canon
        canon.set_context(m.assumptions, m.lengths)
        exactly(m, check_range(m, 0, tail_count(m)))
        p.check_abi(m, windows)
        canon.set_context([], set())

    print('  base paths proved; constructing the group invariant', flush=True)
    start_machine = ind.snapshot(machine)
    start_machine.assumptions += [UGE(group, 1)]
    first = ind.run_to(start_machine, setup.entry, head)
    another = ind.snapshot(first)
    another.assumptions += [UGE(group, 2)]
    second = ind.run_to(another, head, head)
    exactly(second, check_range(second, 0, width))
    general = ind.Generalized(first, second, k)
    if increment:
        counter_invariant(general, first, second, counter, k, width)
    bad = ind.mismatches(first, general, BitVecVal(0, 64))
    if bad:
        raise Unproved(f'invariant differs at entry: {bad}')

    def check(m, how):
        expected = check_range(m, k * width, width)
        if how == 'return':
            if not arm.holds(m, group == k + 1):
                raise Unproved('returns before the last full group')
            expected |= check_range(m, (k + 1) * width, tail_count(m))
            p.check_abi(m, windows)
        exactly(m, expected)
    # Reuse the model's proved small-term facts for this symbolic pass
    # and its tail, as the bounded x86 proofs do for concrete passes.
    if increment:
        p.d_row_facts(first, counter + width * k, 2 * width, flag_words)
        first.fact_symbols.add('len_k')
    print('  initial invariant checked; proving its step and tails', flush=True)
    kinds = ind.loop_step(general, first, k,
                          list(first.assumptions) + [ULT(k, group), ULE(k, bound - 1)], head, check)
    return kinds
