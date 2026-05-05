#!/usr/bin/env python3
# Copyright (c) The mlkem-native project authors
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

import hashlib
import os
import subprocess
import sys
import argparse
from pathlib import Path


# Check if we need to use a wrapper for execution (e.g. QEMU)
exec_prefix = os.environ.get("EXEC_WRAPPER", "")
exec_prefix = exec_prefix.split(" ") if exec_prefix != "" else []


def err(msg, **kwargs):
    print(msg, file=sys.stderr, **kwargs)


def info(msg, **kwargs):
    print(msg, **kwargs)


def read_meta_hashes():
    hashes = {}
    current_name = None
    with open("META.yml") as f:
        for line in f:
            line = line.strip()
            if line.startswith("- name:"):
                current_name = line.split(":", 1)[1].strip()
            elif line.startswith("kat-sha256:") and current_name:
                hashes[current_name] = line.split(":", 1)[1].strip()
    return hashes


def get_kat_binary(level):
    suffix = ".exe" if sys.platform == "win32" else ""
    return Path("test/build") / f"mlkem{level}" / "bin" / f"gen_KAT{level}{suffix}"


def run_kat_single(scheme_name, level, ref_hash):
    binary = get_kat_binary(level)

    if not binary.exists():
        err(f"Binary not found: {binary}")
        return False

    cmd = exec_prefix + [str(binary)]
    result = subprocess.run(cmd, capture_output=True)

    if result.returncode != 0:
        err("FAIL!")
        err(f"{cmd} failed with error code {result.returncode}")
        err(result.stderr.decode("utf-8", errors="replace"))
        return False

    computed = hashlib.sha256(result.stdout).hexdigest()

    if computed == ref_hash:
        info(f"META.yml {scheme_name} kat-sha256: OK")
        return True
    else:
        err(f"META.yml {scheme_name} kat-sha256: FAIL ({ref_hash} != {computed})")
        return False


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--scheme",
        choices=["512", "768", "1024"],
        help="Run KAT for only one parameter set (default: all)",
    )
    args = parser.parse_args()

    all_schemes = [("ML-KEM-512", 512), ("ML-KEM-768", 768), ("ML-KEM-1024", 1024)]
    if args.scheme is not None:
        schemes = [s for s in all_schemes if str(s[1]) == args.scheme]
    else:
        schemes = all_schemes

    ref_hashes = read_meta_hashes()

    failed = False
    for scheme_name, level in schemes:
        if scheme_name not in ref_hashes:
            err(f"META.yml: no kat-sha256 entry for {scheme_name}")
            failed = True
            continue
        if not run_kat_single(scheme_name, level, ref_hashes[scheme_name]):
            failed = True

    if failed:
        sys.exit(1)

    info("ALL GOOD!")


if __name__ == "__main__":
    main()
