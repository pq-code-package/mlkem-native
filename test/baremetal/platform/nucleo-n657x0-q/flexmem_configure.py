#!/usr/bin/env python3
# Copyright (c) The mlkem-native project authors
# Copyright (c) Arm Ltd.
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

"""
Configure STM32N6 FLEXMEM before loading RAM-resident test images.

The helper downloads ``flexmem_config.elf`` into the reset-time memory layout
and starts it directly from RAM. It polls ``SYSCFG->CM55TCMCR`` until the
requested TCM split is visible over SWD, then resets the target so the next ELF
can be loaded into the expanded ITCM/DTCM layout.
"""

import os
import re
import logging
import sys
import time

from nucleo_host.st_tools import connect_args as st_connect_args
from nucleo_host.st_tools import (
    find_cubeprogrammer_cli as st_find_cubeprogrammer_cli,
)
from nucleo_host.st_tools import run_quiet
from nucleo_host.flexmem import flexmem_config_build_instructions
from nucleo_host.symbols import resolve_symbol_with_nm

DONE = "FLEXMEM configuration complete; reset target and load test binary."

# The config ELF writes SYSCFG->CM55TCMCR.  Polling the register via SWD proves
# that the new ITCM/DTCM split latched before the next test binary is loaded.
CM55TCMCR_ADDR = "0x56008008"
CM55TCMCR_EXPECTED_MASK = 0xFF
CM55TCMCR_EXPECTED_VALUE = 0x99

LOG = logging.getLogger(__name__)


def configure_logging():
    """Configure logging, using ``FLEXMEM_VERBOSE`` as the debug switch."""
    level = (
        logging.DEBUG if os.environ.get("FLEXMEM_VERBOSE") else logging.INFO
    )
    logging.basicConfig(level=level, format="%(message)s")


def log_output(output, level):
    """Log multiline CubeProgrammer output at the requested level."""
    if not output:
        return
    for line in output.rstrip().splitlines():
        LOG.log(level, line)


def err(msg):
    """Report a user-visible error line."""
    LOG.error("%s", msg)


def find_cubeprogrammer_cli(cp_path):
    """Find ``STM32_Programmer_CLI`` using platform environment defaults."""
    return st_find_cubeprogrammer_cli(
        cp_path, os.environ.get("ST_CUBE_CLT_ROOT", "")
    )


def cubeprogrammer_cli():
    """Return the CubeProgrammer CLI path, or report a helpful error."""
    cli = find_cubeprogrammer_cli(os.environ.get("ST_CUBE_PROG_PATH", ""))
    if cli is None:
        err(
            "STM32_Programmer_CLI not found; set ST_CUBE_PROG_PATH or "
            "ST_CUBE_CLT_ROOT"
        )
    return cli


def connect_args(mode=None):
    """Build CubeProgrammer SWD connection arguments from the environment."""
    # Keep all CubeProgrammer calls on the same probe, speed, and access port.
    return st_connect_args(
        speed=os.environ.get("STLINK_SPEED", "200"),
        serial=os.environ.get("STLINK_SERIAL", ""),
        apid=os.environ.get("STLINK_APID", ""),
        mode=(
            mode if mode is not None else os.environ.get("STLINK_CONNECT_MODE")
        ),
    )


def reset_target(cli):
    """Best-effort target reset through CubeProgrammer."""
    # Reset is best-effort: the subsequent download/halt sequence reports hard
    # failures.
    args = ["-c", "port=SWD", f"freq={os.environ.get('STLINK_SPEED', '200')}"]
    serial = os.environ.get("STLINK_SERIAL", "")
    if serial:
        args.append(f"sn={serial}")
    return run_quiet([cli] + args + ["-rst"]).returncode == 0


def resolve_symbol(elf, symbol):
    """Resolve a symbol with ``nm`` for direct RAM launch setup."""
    # Resolve entry/stack symbols up front so CubeProgrammer can start from RAM
    # directly.
    return resolve_symbol_with_nm(
        elf, symbol, nm=os.environ.get("NM", "arm-none-eabi-nm")
    )


def read_flexmem_value(cli):
    """Read the FLEXMEM TCM configuration register via SWD HOTPLUG mode."""
    # HOTPLUG reads avoid resetting the core while the config ELF is parked at
    # BKPT.
    cp = run_quiet(
        [cli] + connect_args("HOTPLUG") + ["-r32", CM55TCMCR_ADDR, "1"]
    )
    if os.environ.get("FLEXMEM_VERBOSE"):
        log_output(cp.stdout, logging.DEBUG)
    if cp.returncode != 0:
        return None
    match = re.search(
        rf"{re.escape(CM55TCMCR_ADDR)}\s*:\s*([0-9a-fA-F]{{8}})", cp.stdout
    )
    if not match:
        return None
    return int(match.group(1), 16)


def wait_for_flexmem(cli, timeout_s):
    """Poll until the FLEXMEM register reports the expected expanded layout."""
    # The register update is fast, but polling absorbs probe/transport latency.
    deadline = time.time() + timeout_s
    while time.time() < deadline:
        value = read_flexmem_value(cli)
        if (
            value is not None
            and (value & CM55TCMCR_EXPECTED_MASK) == CM55TCMCR_EXPECTED_VALUE
        ):
            return True
        time.sleep(0.2)
    return False


def main():
    """Download and run the config ELF, then verify the latched layout."""
    configure_logging()

    if len(sys.argv) != 2:
        err(f"Usage: {sys.argv[0]} path/to/flexmem_config.elf")
        return 2

    elf = os.path.abspath(sys.argv[1])
    if not os.path.exists(elf):
        err(f"Config ELF not found: {elf}")
        err(flexmem_config_build_instructions(elf))
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

    # Load the RAM-only config image and seed MSP/PC explicitly because no
    # flash boot flow participates in this helper binary.
    cmd = (
        [cli]
        + connect_args()
        + [
            "-halt",
            "-d",
            elf,
            "-coreReg",
            f"MSP={estack_addr}",
            f"PC={main_thumb}",
            "-run",
        ]
    )
    cp = run_quiet(cmd)
    if os.environ.get("FLEXMEM_VERBOSE") or cp.returncode != 0:
        log_output(
            cp.stdout, logging.DEBUG if cp.returncode == 0 else logging.ERROR
        )
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
