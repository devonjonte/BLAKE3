#!/usr/bin/env python3
"""Executable correctness and structural controls. These are tests, not proofs.

    python3 test_adler32.py --out NEW_DIRECTORY

No clock is read. The compiled function is tested against fixed vectors and
Python's independent zlib, including read-only input ending at a guard page.
"""
import argparse
import ctypes
import importlib.util
import json
from pathlib import Path
import random
import subprocess
import unittest
import zlib

HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location("observe", HERE.parents[1] / "observe.py")
observe = importlib.util.module_from_spec(spec)
spec.loader.exec_module(observe)
OUT = None


class AdlerTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        OUT.mkdir(parents=True, exist_ok=False)
        cls.source = (HERE / "adler32.ode").read_text()
        cls.base = cls.build("baseline", cls.source)
        cls.compact = cls.build("compact", (HERE / "adler32_compact.ode").read_text())

    @classmethod
    def build(cls, name, source):
        p = OUT / f"{name}.ode"
        p.write_text(source)
        r = observe.observe(p, "adler32", OUT / name)
        observe.run(["cc", "-shared", OUT / name / "function.o", "-o", OUT / name / "function.so"])
        lib = ctypes.CDLL(str(OUT / name / "function.so"))
        fn = lib.b3l_adler32
        fn.argtypes = [ctypes.c_void_p, ctypes.c_uint64]
        fn.restype = ctypes.c_uint64
        return r, fn, lib

    def test_01_fixed_vectors_and_zlib(self):
        for variant in [self.base, self.compact]:
            self.check_vectors(variant[1])

    def check_vectors(self, fn):
        for data, expected in [(b"", 1), (b"a", 0x00620062),
                               (b"Wikipedia", 0x11e60398), (b"123456789", 0x091e01de)]:
            self.assertEqual(fn(data, len(data)), expected)
        for b in range(256):
            data = bytes([b])
            self.assertEqual(fn(data, 1), zlib.adler32(data))
        rng = random.Random(0xAD1E32)
        lengths = [0, 1, 2, 3, 15, 16, 63, 64, 255, 256, 257, 5551, 5552, 5553,
                   65520, 65521, 65522, 65535, 65536]
        for n in lengths:
            for data in [bytes(n), bytes([255]) * n, bytes(i % 256 for i in range(n)), rng.randbytes(n)]:
                original = bytes(data)
                self.assertEqual(fn(data, n), zlib.adler32(data), f"length {n}")
                self.assertEqual(data, original, "input is unchanged")
        self.assertEqual(fn(None, 0), 1, "empty input is not dereferenced")

    def test_02_read_only_input_between_guards(self):
        # Run separately: a planted out-of-bounds access should fail this test,
        # rather than end the rest of the test driver's controls.
        child = r'''
import ctypes, os, resource, sys, zlib
resource.setrlimit(resource.RLIMIT_CORE, (0, 0))
lib = ctypes.CDLL(sys.argv[1]); fn = lib.b3l_adler32
fn.argtypes = [ctypes.c_void_p, ctypes.c_uint64]; fn.restype = ctypes.c_uint64
c = ctypes.CDLL(None, use_errno=True)
c.mmap.argtypes = [ctypes.c_void_p, ctypes.c_size_t, ctypes.c_int, ctypes.c_int, ctypes.c_int, ctypes.c_long]
c.mmap.restype = ctypes.c_void_p
c.mprotect.argtypes = [ctypes.c_void_p, ctypes.c_size_t, ctypes.c_int]
c.munmap.argtypes = [ctypes.c_void_p, ctypes.c_size_t]
p = os.sysconf('SC_PAGE_SIZE'); base = c.mmap(None, 3*p, 0, 0x22, -1, 0)
assert base != ctypes.c_void_p(-1).value
for n in [0, 1, 2, 15, 16, 63, 64, 255, p-1, p]:
    for at in [base+2*p-n, base+p]:
        assert c.mprotect(base+p, p, 3) == 0
        data = bytes((i*17+23)%256 for i in range(n))
        ctypes.memmove(at, data, n)
        assert c.mprotect(base+p, p, 1) == 0
        assert fn(at, n) == zlib.adler32(data)
assert c.munmap(base, 3*p) == 0
'''
        for variant in ["baseline", "compact"]:
            observe.run(["python3", "-c", child, OUT / variant / "function.so"])
        # Positive control for the guard: make a read one byte too far. The
        # first nonempty suffix ends at the inaccessible page and must fault.
        self.build("overread", self.source.replace("u8[input + i]", "u8[input + i + 1]"))
        with self.assertRaises(subprocess.CalledProcessError) as failure:
            observe.run(["python3", "-c", child, OUT / "overread" / "function.so"])
        self.assertIn(failure.exception.returncode, [-11, -7], "guard catches an actual memory fault")

    def test_03_unrelated_source_leaves_exact_function_bytes(self):
        noise = "\nfn unrelated(x)\n{\n  return x + 123\n}\n"
        variants = {"repeat": self.source, "appended": self.source + noise,
                    "prepended": noise + self.source, "comment": "// An unrelated edit.\n" + self.source}
        for name, src in variants.items():
            r, _, _ = self.build(name, src)
            self.assertEqual(r["text"], self.base[0]["text"], name)
            self.assertEqual(r["layout"], self.base[0]["layout"], name)
        # A positive control: changing the target changes its bytes and answer.
        _, broken, _ = self.build("wrong-seed", self.source.replace("var a = 1", "var a = 2"))
        mutant = json.loads((OUT / "wrong-seed" / "report.json").read_text())
        self.assertNotEqual(mutant["text"], self.base[0]["text"])
        self.assertNotEqual(broken(b"Wikipedia", 9), 0x11e60398)

    def test_04_equivalent_spelling_changes_structure(self):
        a, b = self.base[0], self.compact[0]
        self.assertNotEqual(a["text"], b["text"])
        self.assertEqual(a["static_instructions"] - b["static_instructions"], 2)
        self.assertEqual(a["layout"], b["layout"])

    def test_05_missing_function_is_loud(self):
        with self.assertRaisesRegex(ValueError, "no function named"):
            observe.observe(HERE / "adler32.ode", "misspelled", OUT / "missing")

    def test_06_disassembly_reader(self):
        self.assertEqual(observe.instructions("0000 <name>:\n  0: push rbx\n  1: ret\n"), ["push rbx", "ret"])


if __name__ == "__main__":
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--out", type=Path, required=True)
    args = ap.parse_args()
    OUT = args.out.resolve()
    unittest.main(argv=[__file__], verbosity=2)
