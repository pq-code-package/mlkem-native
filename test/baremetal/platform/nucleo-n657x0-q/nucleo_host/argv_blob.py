# Copyright (c) The mlkem-native project authors
# Copyright (c) Arm Ltd.
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

"""Build the target-resident argv block consumed by ``__wrap_main``."""

import struct as st

ARGV_BLOCK_SIZE = 64 * 1024


def pack_cmdline(args, base_addr, block_size=ARGV_BLOCK_SIZE):
    """
    Return a padded little-endian argv blob for the STM32 baremetal target.

    The blob starts with ``uint32_t argc`` followed by ``uint32_t argv[argc]``.
    Each argv entry is an absolute target address pointing at a NUL-terminated
    UTF-8 string stored later in the same blob.  The result is padded to the
    full target reservation so GDB ``restore`` overwrites stale contents.
    """
    argc = len(args)
    header_sz = 4 + 4 * argc
    ptrs = []
    strings = b""
    cur = 0
    for arg in args:
        encoded = arg.encode("utf-8") + b"\x00"
        # GDB writes the blob at ``base_addr``; the C side expects argv
        # pointers to be valid target addresses rather than blob offsets.
        ptrs.append(base_addr + header_sz + cur)
        strings += encoded
        cur += len(encoded)
    blob = st.pack("<I", argc) + b"".join(st.pack("<I", ptr) for ptr in ptrs) + strings
    if len(blob) > block_size:
        raise ValueError(
            f"argv blob is {len(blob)} bytes, exceeds {block_size}-byte block"
        )
    return blob + bytes(block_size - len(blob))
