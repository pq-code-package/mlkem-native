# Copyright (c) The mlkem-native project authors
# Copyright (c) The mldsa-native project authors
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
#
# Post-processes armasm64 output: changes the relocations in .pdata
# from IMAGE_REL_ARM64_ADDR64 to IMAGE_REL_ARM64_ADDR32NB, because
# armasm64 cannot emit RVA relocations for hand-written unwind data.
#
# This python script was provided by Claude (Anthropic)
#

import struct, sys

ADDR64, ADDR32NB = 14, 2

path = sys.argv[1]
data = bytearray(open(path, "rb").read())

machine, nsec, _, symptr, nsyms, optsz, _ = struct.unpack_from("<HHIIIHH", data, 0)
assert machine == 0xAA64, f"not an ARM64 object (machine=0x{machine:x})"

sec_off = 20 + optsz
for i in range(nsec):
    off = sec_off + i * 40
    name = bytes(data[off:off+8]).rstrip(b"\0")
    (relptr,) = struct.unpack_from("<I", data, off + 24)
    (nrel,)   = struct.unpack_from("<H", data, off + 32)
    if name != b".pdata":
        continue
    for r in range(nrel):
        r_off = relptr + r * 10
        va, symidx, typ = struct.unpack_from("<IIH", data, r_off)
        print(f".pdata reloc @0x{va:x} sym {symidx} type {typ}")
        if typ == ADDR64:
            struct.pack_into("<H", data, r_off + 8, ADDR32NB)
            print("  -> patched to ADDR32NB")

open(path, "wb").write(data)
