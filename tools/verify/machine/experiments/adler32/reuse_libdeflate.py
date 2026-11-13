#!/usr/bin/env python3
"""Use the existing proved Ode project inside libdeflate's zlib-format paths.

    python3 reuse_libdeflate.py PINNED_LIBDEFLATE_SOURCE NEW_OUTPUT

Linux x86-64 only. Builds/checks Ode normally; copies the dependency and changes
only its two whole-buffer checksum calls plus the declaration/link scaffolding.
The original checkout and its incremental public Adler API stay unchanged.
Run under a bounded process-group supervisor. This test collects no timings.
"""
import argparse
import ctypes as C
import difflib
import json
import platform
from pathlib import Path
import random
import re
import shutil
import subprocess
import zlib
from prepare_bench import DEPS

HERE = Path(__file__).resolve().parent


def run(args, log):
    with log.open("w") as f:
        subprocess.run(["timeout", "-k", "5", "180", *map(str, args)], stdout=f,
                       stderr=subprocess.STDOUT, check=True, timeout=190)


def load(path):
    lib = C.CDLL(str(path), mode=C.RTLD_LOCAL)
    signatures = {
        "alloc_compressor": (C.c_void_p, [C.c_int]),
        "free_compressor": (None, [C.c_void_p]),
        "alloc_decompressor": (C.c_void_p, []),
        "free_decompressor": (None, [C.c_void_p]),
        "zlib_compress_bound": (C.c_size_t, [C.c_void_p, C.c_size_t]),
        "zlib_compress": (C.c_size_t, [C.c_void_p, C.c_void_p, C.c_size_t, C.c_void_p, C.c_size_t]),
        "zlib_decompress": (C.c_int, [C.c_void_p, C.c_void_p, C.c_size_t, C.c_void_p, C.c_size_t, C.POINTER(C.c_size_t)]),
        "adler32": (C.c_uint32, [C.c_uint32, C.c_void_p, C.c_size_t]),
    }
    for name, (result, args) in signatures.items():
        fn = getattr(lib, "libdeflate_" + name)
        fn.restype, fn.argtypes = result, args
    return lib


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("source", type=Path)
    ap.add_argument("out", type=Path)
    a = ap.parse_args()
    assert platform.system() == "Linux" and platform.machine() == "x86_64"
    source, out = a.source.resolve(), a.out.resolve()
    rev = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=source, text=True).strip()
    assert rev == DEPS["libdeflate"][0]
    subprocess.run(["git", "diff", "--exit-code", "HEAD"], cwd=source, check=True, capture_output=True)
    out.mkdir(parents=True, exist_ok=False)
    proved = out / "proved"
    run(["sh", HERE / "build.sh", proved], out / "ode-build.log")
    report = json.loads((proved / "report.json").read_text())
    assert report["proof"].startswith("Lean checked Proof_adler32.adler32_meets")
    modified = out / "source"
    shutil.copytree(source, modified, ignore=shutil.ignore_patterns(".git"))
    changes = []
    for name, old, new in [
        ("lib/zlib_compress.c", "libdeflate_adler32(1, in, in_nbytes)", "(u32)b3l_adler32(in, in_nbytes)"),
        ("lib/zlib_decompress.c", "libdeflate_adler32(1, out, actual_out_nbytes)", "(u32)b3l_adler32(out, actual_out_nbytes)"),
    ]:
        p = modified / name
        original = p.read_text()
        assert original.count(old) == 1
        changed = original.replace(old, new).replace('#include "zlib_constants.h"', '#include "zlib_constants.h"\n#include "ode_adler32.h"')
        p.write_text(changed)
        changes.extend(difflib.unified_diff(original.splitlines(True), changed.splitlines(True), fromfile="a/"+name, tofile="b/"+name))
    header = modified / "lib/ode_adler32.h"
    header.write_text('/* Experiment: original proved Ode checksum, seed 1, readable buffer. */\n#include <stdint.h>\n#include <stddef.h>\n_Static_assert(sizeof(size_t) == sizeof(uint64_t), "Ode ABI needs 64-bit size_t");\nextern uint64_t b3l_adler32(const void *input, uint64_t length);\n')
    changes.extend(difflib.unified_diff([], header.read_text().splitlines(True), fromfile="/dev/null", tofile="b/lib/ode_adler32.h"))
    p = modified / "CMakeLists.txt"
    original = p.read_text()
    changed = original + '\n# Experiment: link the object produced by the proof-first Ode build.\ntarget_sources(libdeflate_shared PRIVATE "${ODE_ADLER_OBJECT}")\n'
    p.write_text(changed)
    changes.extend(difflib.unified_diff(original.splitlines(True), changed.splitlines(True), fromfile="a/CMakeLists.txt", tofile="b/CMakeLists.txt"))
    (out / "integration.patch").write_text("".join(changes))
    for name, src in [("native", source), ("ode", modified)]:
        build = out / name
        cmd = ["cmake", "-S", src, "-B", build, "-DCMAKE_BUILD_TYPE=Release", "-DLIBDEFLATE_BUILD_STATIC_LIB=OFF", "-DLIBDEFLATE_BUILD_GZIP=OFF"]
        if name == "ode": cmd += ["-DODE_ADLER_OBJECT=" + str(proved / "function.o")]
        run(cmd, out / f"{name}-configure.log")
        run(["cmake", "--build", build, "-j", "4"], out / f"{name}-build.log")
    library = out / "ode/libdeflate.so"
    # The shared object's function must still have the exact proved bytes.
    sections = subprocess.check_output(["readelf", "-WS", library], text=True)
    text = re.search(r"\]\s+\.text\s+PROGBITS\s+([0-9a-f]+)\s+([0-9a-f]+)", sections)
    symbols = subprocess.check_output(["nm", "-an", library], text=True)
    symbol = re.search(r"^([0-9a-f]+) [tT] b3l_adler32$", symbols, re.M)
    assert text and symbol
    position = int(text[2], 16) + int(symbol[1], 16) - int(text[1], 16)
    expected = (proved / "text.bin").read_bytes()
    assert library.read_bytes()[position:position+len(expected)] == expected, "consumer changed the proved function"
    (out / "linked-ode.txt").write_text(subprocess.check_output(["objdump", "-d", "--disassemble=b3l_adler32", library], text=True))
    native, ode = load(out / "native/libdeflate.so"), load(library)
    rng = random.Random(0xAD1E32)
    cases = [b"", b"a", b"Wikipedia", b"123456789"]
    for n in [16, 64, 256, 4096, 5551, 5552, 5553, 65536, 1048576]:
        cases += [bytes(n), bytes([255])*n, bytes(i % 256 for i in range(n)), rng.randbytes(n)]
    checked, bad_checksums = 0, 0
    for level in [1, 6, 12]:
        compressors = [lib.libdeflate_alloc_compressor(level) for lib in [native, ode]]
        decompressors = [lib.libdeflate_alloc_decompressor() for lib in [native, ode]]
        assert all(compressors) and all(decompressors)
        try:
            for data in cases:
                src = C.create_string_buffer(data)
                streams = []
                for lib, compressor in zip([native, ode], compressors):
                    cap = lib.libdeflate_zlib_compress_bound(compressor, len(data))
                    buf = C.create_string_buffer(cap)
                    n = lib.libdeflate_zlib_compress(compressor, src, len(data), buf, cap)
                    assert n
                    stream = buf.raw[:n]
                    assert zlib.decompress(stream) == data
                    streams.append(stream)
                assert streams[0] == streams[1], "checksum substitution changed the zlib stream"
                for stream in [*streams, zlib.compress(data)]:
                    packed = C.create_string_buffer(stream)
                    for lib, decompressor in zip([native, ode], decompressors):
                        dest = C.create_string_buffer(len(data)+17)
                        count = C.c_size_t()
                        assert lib.libdeflate_zlib_decompress(decompressor, packed, len(stream), dest, len(dest), C.byref(count)) == 0
                        assert count.value == len(data) and dest.raw[:count.value] == data
                for i in range(4):
                    bad = bytearray(streams[0]); bad[-1-i] ^= 1
                    packed = C.create_string_buffer(bytes(bad))
                    for lib, decompressor in zip([native, ode], decompressors):
                        dest = C.create_string_buffer(len(data)+17); count = C.c_size_t()
                        assert lib.libdeflate_zlib_decompress(decompressor, packed, len(bad), dest, len(dest), C.byref(count)) == 1, "changed checksum must be rejected"
                    bad_checksums += 1
                # The general incremental public Adler API is deliberately intact.
                half = len(data)//2
                seed = ode.libdeflate_adler32(1, src, half)
                assert ode.libdeflate_adler32(seed, C.byref(src, half), len(data)-half) == zlib.adler32(data)
                checked += 1
        finally:
            for lib, compressor, decompressor in zip([native, ode], compressors, decompressors):
                lib.libdeflate_free_compressor(compressor); lib.libdeflate_free_decompressor(decompressor)
    summary = {"libdeflate_commit": rev, "python_zlib": zlib.ZLIB_RUNTIME_VERSION,
               "input_level_cases": checked, "corrupt_trailer_cases": bad_checksums,
               "levels": [1, 6, 12], "linked_proved_bytes": len(expected),
               "claims": "executable integration checks; only the unchanged Ode callee has the machine-code theorem; no timing performed"}
    (out / "summary.json").write_text(json.dumps(summary, indent=2)+"\n")
    print(json.dumps(summary, indent=2))


if __name__ == "__main__":
    main()
