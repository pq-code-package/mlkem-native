#!/usr/bin/env python3
# Copyright (c) The mldsa-native project authors
# Copyright (c) The mlkem-native project authors
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

"""QEMU wrapper for executing Cortex-M33 bare-metal ELF binaries (mps3-an524)."""

import struct as st
import sys
import subprocess
import tempfile
import os


def err(msg, **kwargs):
    print(msg, file=sys.stderr, **kwargs)


binpath = sys.argv[1]
args = sys.argv[1:]

# Memory layout: [argc] [offset1] [offset2] ... [string1\0] [string2\0] ...
# M33-AN524 RAM: 0x20000000-0x2001FFFF (128KB)
# Heap ends at: ~0x20000b20
# Stack: 0x20008000-0x2001FFFF (96KB, grows downward)
# Use address after heap but before stack
# cmdline.c CMDLINE_ADDR must match this value
cmdline_offset = 0x20007000
arg0_offset = cmdline_offset + 4 + len(args) * 4
arg_offsets = [sum(map(len, args[:i])) + i + arg0_offset for i in range(len(args))]

binargs = st.pack(
    f"<{1+len(args)}I" + "".join(f"{len(a)+1}s" for a in args),
    len(args),
    *arg_offsets,
    *map(lambda x: x.encode("utf-8"), args),
)

with tempfile.NamedTemporaryFile(mode="wb", delete=False, suffix=".bin") as fd:
    args_file = fd.name
    fd.write(binargs)

try:
    qemu_cmd = f"qemu-system-arm -M mps3-an524 -cpu cortex-m33 -nographic -semihosting -kernel {binpath} -device loader,file={args_file},addr=0x{cmdline_offset:x}".split()
    result = subprocess.run(qemu_cmd, encoding="utf-8", capture_output=True)
finally:
    os.unlink(args_file)
if result.returncode != 0:
    err("FAIL!")
    err(f"{qemu_cmd} failed with error code {result.returncode}")
    err(result.stderr)
    exit(1)

for line in result.stdout.splitlines():
    print(line)
