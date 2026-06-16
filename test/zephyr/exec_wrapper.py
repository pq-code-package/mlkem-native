#!/usr/bin/env python3
# Copyright (c) The mlkem-native project authors
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

# Runs a Zephyr ELF under QEMU (machine from QEMU_MACHINE, set in platform.mk).
# Extra args reach the guest via semihosting (see app/shim.c), the UART console
# goes to stdout via -nographic, and the guest's semihosting exit sets QEMU's
# return code.

import os
import sys
import subprocess

binpath = sys.argv[1]
args = sys.argv[2:]
machine = os.environ.get("QEMU_MACHINE", "mps3-an547")

semihosting_args = [binpath] + args
semihosting_config = "enable=on," + ",".join(f"arg={a}" for a in semihosting_args)

qemu_cmd = [
    "qemu-system-arm",
    "-M",
    machine,
    "-monitor",
    "none",
    "-nographic",
    "-semihosting-config",
    semihosting_config,
    "-kernel",
    binpath,
]

result = subprocess.run(qemu_cmd, encoding="utf-8", capture_output=True, timeout=300)
sys.stdout.write(result.stdout)
if result.returncode != 0:
    sys.stderr.write(result.stderr)
sys.exit(result.returncode)
