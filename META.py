#!/usr/bin/env python3
# Copyright (c) The mlkem-native project authors
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

# Checks the KAT output of a gen_KAT binary against META.yml.
#
# Reads the KAT bytes from stdin, hashes them with SHA-256, and compares
# against the kat-sha256 field for the given scheme in META.yml. If stdin is
# "SKIPPED" (emitted by gen_KAT for reduced-API builds), the check is reported
# as skipped.
#
# To run manually, pipe a gen_KAT binary into it, e.g.:
#
#   test/build/mlkem512/bin/gen_KAT512 | python3 META.py --scheme 512

import hashlib
import sys
import argparse


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


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--scheme",
        choices=["512", "768", "1024"],
        required=True,
        help="Parameter set whose KAT output is being checked",
    )
    args = parser.parse_args()

    scheme_name = f"ML-KEM-{args.scheme}"
    ref = read_meta_hashes().get(scheme_name)
    if ref is None:
        err(f"META.yml: no kat-sha256 entry for {scheme_name}")
        sys.exit(1)

    # Read the raw bytes piped in from gen_KAT on stdin. Read in binary mode so
    # that no newline translation occurs on Windows.
    data = sys.stdin.buffer.read()

    # Reduced-API builds emit "SKIPPED" instead of KAT bytes; report as skipped.
    if data.startswith(b"SKIPPED"):
        info(f"META.yml {scheme_name} kat-sha256: SKIPPED")
        sys.exit(0)

    computed = hashlib.sha256(data).hexdigest()

    if computed == ref:
        info(f"META.yml {scheme_name} kat-sha256: OK")
    else:
        err(f"META.yml {scheme_name} kat-sha256: FAIL ({ref} != {computed})")
        sys.exit(1)


if __name__ == "__main__":
    main()
