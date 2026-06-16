#!/usr/bin/env python3
# Copyright (c) The mlkem-native project authors
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

# Runs a Zephyr ELF for an Arm MPS board under QEMU. The QEMU machine is taken
# from MLK_QEMU_MACHINE (set per target in platform.mk). Any extra arguments
# (used by the acvp/wycheproof tests) are handed to the guest via semihosting
# SYS_GET_CMDLINE (see app/shim.c); the application console (UART) is routed to
# stdout via -nographic; and the test stops the machine through a semihosting
# exit, so QEMU's return code reflects the test's pass/fail status.

import os
import sys
import subprocess

binpath = sys.argv[1]
args = sys.argv[2:]
machine = os.environ.get("MLK_QEMU_MACHINE", "mps3-an547")

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
