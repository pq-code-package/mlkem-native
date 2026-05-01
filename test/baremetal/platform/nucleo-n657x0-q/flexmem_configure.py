#!/usr/bin/env python3
"""
/*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */
"""

# Configure STM32N6 FLEXMEM before loading the RAM-resident test image.

import os
import re
import logging
import shutil
import subprocess
import sys
import time

DONE = "FLEXMEM configuration complete; reset target and load test binary."

# The config ELF writes SYSCFG->CM55TCMCR.  Polling the register via SWD proves
# that the new ITCM/DTCM split latched before the next test binary is loaded.
CM55TCMCR_ADDR = "0x56008008"
CM55TCMCR_EXPECTED_MASK = 0xFF
CM55TCMCR_EXPECTED_VALUE = 0x99

LOG = logging.getLogger(__name__)


def configure_logging():
    level = logging.DEBUG if os.environ.get("FLEXMEM_VERBOSE") else logging.INFO
    logging.basicConfig(level=level, format="%(message)s")


def log_output(output, level):
    if not output:
        return
    for line in output.rstrip().splitlines():
        LOG.log(level, line)


def err(msg):
    LOG.error("%s", msg)


def find_cubeprogrammer_cli(cp_path):
    # Accept a direct binary path, a CubeProgrammer directory, a CubeCLT root, or PATH.
    candidates = []
    if cp_path:
        if os.path.isdir(cp_path):
            candidates.extend([
                os.path.join(cp_path, "STM32_Programmer_CLI"),
                os.path.join(cp_path, "bin", "STM32_Programmer_CLI"),
            ])
        else:
            candidates.append(cp_path)
    st_clt_root = os.environ.get("ST_CUBE_CLT_ROOT", "")
    if st_clt_root:
        candidates.append(os.path.join(st_clt_root, "STM32CubeProgrammer", "bin", "STM32_Programmer_CLI"))
    path_candidate = shutil.which("STM32_Programmer_CLI")
    if path_candidate:
        candidates.append(path_candidate)
    for candidate in candidates:
        if candidate and os.path.isfile(candidate) and os.access(candidate, os.X_OK):
            return candidate
    return None


def cubeprogrammer_cli():
    cli = find_cubeprogrammer_cli(os.environ.get("ST_CUBE_PROG_PATH", ""))
    if cli is None:
        err("STM32_Programmer_CLI not found; set ST_CUBE_PROG_PATH or ST_CUBE_CLT_ROOT")
    return cli


def connect_args(mode=None):
    # Keep all CubeProgrammer calls on the same probe, speed, and access port.
    args = ["-c", "port=SWD", f"freq={os.environ.get('STLINK_SPEED', '200')}"]
    connect_mode = mode if mode is not None else os.environ.get("STLINK_CONNECT_MODE")
    if connect_mode:
        args.append(f"mode={connect_mode}")
    serial = os.environ.get("STLINK_SERIAL", "")
    apid = os.environ.get("STLINK_APID", "")
    if serial:
        args.append(f"sn={serial}")
    if apid:
        args.append(f"ap={apid}")
    return args


def run_quiet(cmd):
    return subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)


def reset_target(cli):
    # Reset is best-effort: the subsequent download/halt sequence reports hard failures.
    args = ["-c", "port=SWD", f"freq={os.environ.get('STLINK_SPEED', '200')}"]
    serial = os.environ.get("STLINK_SERIAL", "")
    if serial:
        args.append(f"sn={serial}")
    return run_quiet([cli] + args + ["-rst"]).returncode == 0


def resolve_symbol(elf, symbol):
    # Resolve entry/stack symbols up front so CubeProgrammer can start from RAM directly.
    nm = os.environ.get("NM", "arm-none-eabi-nm")
    try:
        cp = subprocess.run([nm, "-n", elf], stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
    except OSError:
        return None
    if cp.returncode != 0:
        return None
    for line in cp.stdout.splitlines():
        fields = line.split()
        if len(fields) >= 3 and fields[-1] == symbol:
            return "0x" + fields[0].lstrip("0x")
    return None


def read_flexmem_value(cli):
    # HOTPLUG reads avoid resetting the core while the config ELF is parked at BKPT.
    cp = run_quiet([cli] + connect_args("HOTPLUG") + ["-r32", CM55TCMCR_ADDR, "1"])
    if os.environ.get("FLEXMEM_VERBOSE"):
        log_output(cp.stdout, logging.DEBUG)
    if cp.returncode != 0:
        return None
    match = re.search(rf"{re.escape(CM55TCMCR_ADDR)}\s*:\s*([0-9a-fA-F]{{8}})", cp.stdout)
    if not match:
        return None
    return int(match.group(1), 16)


def wait_for_flexmem(cli, timeout_s):
    # The register update is fast, but polling absorbs probe/transport latency.
    deadline = time.time() + timeout_s
    while time.time() < deadline:
        value = read_flexmem_value(cli)
        if value is not None and (value & CM55TCMCR_EXPECTED_MASK) == CM55TCMCR_EXPECTED_VALUE:
            return True
        time.sleep(0.2)
    return False


def main():
    configure_logging()

    if len(sys.argv) != 2:
        err(f"Usage: {sys.argv[0]} path/to/flexmem_config.elf")
        return 2

    elf = os.path.abspath(sys.argv[1])
    if not os.path.exists(elf):
        err(f"Config ELF not found: {elf}")
        return 2

    cli = cubeprogrammer_cli()
    if cli is None:
        return 2

    main_addr = resolve_symbol(elf, "main")
    estack_addr = resolve_symbol(elf, "_estack")
    if main_addr is None or estack_addr is None:
        err("Failed to resolve main/_estack in config ELF")
        return 2
    main_thumb = hex(int(main_addr, 16) | 1)

    timeout_s = float(os.environ.get("FLEXMEM_CONFIG_TIMEOUT", "30"))
    reset_target(cli)

    # Load the RAM-only config image and seed MSP/PC explicitly because no flash
    # boot flow participates in this helper binary.
    cmd = [cli] + connect_args() + ["-halt", "-d", elf, "-coreReg", f"MSP={estack_addr}", f"PC={main_thumb}", "-run"]
    cp = run_quiet(cmd)
    if os.environ.get("FLEXMEM_VERBOSE") or cp.returncode != 0:
        log_output(cp.stdout, logging.DEBUG if cp.returncode == 0 else logging.ERROR)
    if cp.returncode != 0:
        err("FLEXMEM config RAM download/start failed")
        return cp.returncode

    if not wait_for_flexmem(cli, timeout_s):
        err("FLEXMEM configuration register did not reach expected 0x99 value")
        return 124

    LOG.debug("%s", DONE)
    reset_target(cli)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
