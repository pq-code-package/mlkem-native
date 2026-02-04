#!/usr/bin/env python3
# Copyright (c) The mlkem-native project authors
# Copyright (c) Arm Ltd.
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

import os
import struct as st
import sys


def pack_cmdline(args, base_addr):
    """
    Pack argv for the STM32 baremetal target:
      u32 argc
      u32 argv_ptrs[argc]   (absolute addresses: base_addr + string offsets)
      NUL-terminated strings
    All fields are little-endian 32-bit.
    """
    argc = len(args)
    header_sz = 4 + 4 * argc
    ptrs = []
    strings = b""
    cur = 0
    for s in args:
        b = s.encode("utf-8") + b"\x00"
        ptrs.append(base_addr + header_sz + cur)
        strings += b
        cur += len(b)
    return st.pack("<I", argc) + b"".join(st.pack("<I", p) for p in ptrs) + strings


def main(argv):
    if len(argv) < 4:
        print("Usage: make_argv_bin.py <output.bin> <base_addr_hex> <arg0> [arg1 ...]", file=sys.stderr)
        return 2
    out = argv[1]
    base_hex = argv[2]
    try:
        base_addr = int(base_hex, 16)
    except ValueError:
        print(f"Invalid base address hex: {base_hex}", file=sys.stderr)
        return 2
    args = argv[3:]
    blob = pack_cmdline(args, base_addr)
    with open(out, "wb") as f:
        f.write(blob)
    print(f"Wrote {len(blob)} bytes to {os.path.abspath(out)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
