#!/usr/bin/env python3
# Copyright (c) The mlkem-native project authors
# Copyright (c) Arm Ltd.
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

"""Build a standalone packed argv blob for debugger or fixture use."""

import os
import sys

from nucleo_host.argv_blob import pack_cmdline


def main(argv):
    """Parse CLI arguments, write the argv blob, and return a process code."""
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
    # The output format is shared with exec_wrapper.py and consumed directly by
    # the target ``mlk_cmdline_block`` memory reservation.
    blob = pack_cmdline(args, base_addr)
    with open(out, "wb") as f:
        f.write(blob)
    print(f"Wrote {len(blob)} bytes to {os.path.abspath(out)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
