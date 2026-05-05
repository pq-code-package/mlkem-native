#!/usr/bin/env python3
# Copyright (c) The mldsa-native project authors
# Copyright (c) The mlkem-native project authors
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

import sys
import subprocess


def err(msg, **kwargs):
    print(msg, file=sys.stderr, **kwargs)


binpath = sys.argv[1]
args = sys.argv[2:]

# Build semihosting config with command-line arguments
# Each arg is passed as ,arg=<value>
semihosting_args = [binpath] + args
semihosting_config = "enable=on," + ",".join(f"arg={a}" for a in semihosting_args)

qemu_cmd = [
    "qemu-system-aarch64",
    "-M",
    "virt",
    "-cpu",
    "max",
    "-nographic",
    "-semihosting-config",
    semihosting_config,
    "-kernel",
    binpath,
]

result = subprocess.run(qemu_cmd, encoding="utf-8", capture_output=True, timeout=30)
if result.returncode != 0:
    err("FAIL!")
    err(f"{' '.join(qemu_cmd)} failed with error code {result.returncode}")
    err(result.stderr)
    err(result.stdout)
    exit(1)

# QEMU semihosting output goes to stderr, so print that to stdout
for line in result.stderr.splitlines():
    print(line)
