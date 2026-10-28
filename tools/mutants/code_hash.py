"""The SHA-256 of what an ELF executable loads: every section the loader
maps (SHF_ALLOC), its name, address, size and bytes (a NOBITS section's
size alone), but the notes, whose build ID hashes the whole file, debug
info and line tables included. Two executables with the same hash run
the same: the machine code, its data and its relocations are byte for
byte the same. A mutant whose test binaries all hash as the unmutated
build's changes nothing on this machine (test-runner, check.py's "same
code"); one that moves a line moves a panic's location in the read-only
data, so it hashes differently and its tests run.

    python3 tools/mutants/code_hash.py EXECUTABLE
"""

import hashlib
import struct
import sys

SHF_ALLOC = 0x2
SHT_NOBITS = 8
SHT_NOTE = 7


def code_hash(path):
    data = open(path, "rb").read()
    assert data[:4] == b"\x7fELF", f"{path}: not an ELF file"
    assert data[4] == 2 and data[5] == 1, f"{path}: not a 64-bit little-endian ELF file"
    shoff, = struct.unpack_from("<Q", data, 0x28)
    shentsize, shnum, shstrndx = struct.unpack_from("<HHH", data, 0x3A)
    assert shentsize == 64 and shnum > 0, f"{path}: unexpected section headers"

    def header(i):
        return struct.unpack_from("<IIQQQQIIQQ", data, shoff + i * shentsize)

    strtab = header(shstrndx)
    names = data[strtab[4]:strtab[4] + strtab[5]]
    h = hashlib.sha256()
    for i in range(shnum):
        name_off, kind, flags, addr, offset, size = header(i)[:6]
        if not flags & SHF_ALLOC or kind == SHT_NOTE:
            continue
        name = names[name_off:names.index(b"\0", name_off)]
        h.update(struct.pack("<QQQ", len(name), addr, size) + name)
        if kind != SHT_NOBITS:
            h.update(data[offset:offset + size])
    return h.hexdigest()


if __name__ == "__main__":
    print(code_hash(sys.argv[1]))
