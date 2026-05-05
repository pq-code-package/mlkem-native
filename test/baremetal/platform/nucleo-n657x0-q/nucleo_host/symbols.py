# Copyright (c) The mlkem-native project authors
# Copyright (c) Arm Ltd.
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

"""Resolve symbols from ARM ELF files using ``nm`` and ``readelf`` output."""

import shutil
import subprocess


def default_readelf():
    """Return the preferred readelf executable name available on this host."""
    return (
        shutil.which("arm-none-eabi-readelf")
        or shutil.which("readelf")
        or "readelf"
    )


def resolve_symbol(
    elf_path: str, symbol: str, nm="arm-none-eabi-nm", readelf=None
):
    """Resolve ``symbol`` to a hex address."""
    addr = resolve_symbol_with_nm(elf_path, symbol, nm)
    if addr is not None:
        return addr
    return resolve_symbol_with_readelf(
        elf_path, symbol, readelf or default_readelf()
    )


def resolve_symbol_with_nm(elf_path: str, symbol: str, nm="arm-none-eabi-nm"):
    """Resolve ``symbol`` with ``nm -n`` and return ``None`` on any failure."""
    try:
        cp = subprocess.run(
            [nm, "-n", elf_path],
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
        )
    except OSError:
        return None
    if cp.returncode != 0:
        return None
    return parse_nm_symbol(cp.stdout, symbol)


def parse_nm_symbol(output: str, symbol: str):
    """Parse one symbol address from ``nm -n`` output."""
    for line in output.splitlines():
        parts = line.strip().split()
        if len(parts) >= 3 and parts[-1] == symbol:
            addr_hex = parts[0]
            if not addr_hex.startswith("0x"):
                addr_hex = "0x" + addr_hex
            return addr_hex
    return None


def resolve_symbol_with_readelf(elf_path: str, symbol: str, readelf=None):
    """Resolve ``symbol`` with ``readelf -s``."""
    try:
        cp = subprocess.run(
            [readelf or default_readelf(), "-s", elf_path],
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
        )
    except OSError:
        return None
    if cp.returncode != 0:
        return None
    return parse_readelf_symbol(cp.stdout, symbol)


def parse_readelf_symbol(output: str, symbol: str):
    """Parse one symbol address from ``readelf -s`` output."""
    for line in output.splitlines():
        if symbol not in line:
            continue
        fields = line.split()
        if len(fields) >= 8 and fields[-1] == symbol:
            val = fields[1]
            if all(char in "0123456789abcdefABCDEF" for char in val):
                return "0x" + val
    return None
