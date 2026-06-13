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
import logging
import sys
import tempfile

from nucleo_host.flexmem import flexmem_config_build_instructions
from nucleo_host.openocd_tools import find_openocd
from nucleo_host.openocd_tools import flexmem_script_lines
from nucleo_host.openocd_tools import openocd_base_args
from nucleo_host.openocd_tools import run_quiet
from nucleo_host.openocd_tools import serial_from_env
from nucleo_host.openocd_tools import speed_khz_from_env
from nucleo_host.openocd_tools import transport_from_env
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
    level = logging.DEBUG if os.environ.get("FLEXMEM_VERBOSE") else logging.INFO
    logging.basicConfig(level=level, format="%(message)s")


def log_output(output, level):
    """Log multiline subprocess output at the requested level."""
    if not output:
        return
    for line in output.rstrip().splitlines():
        LOG.log(level, line)


def err(msg):
    """Report a user-visible error line."""
    LOG.error("%s", msg)


def resolve_symbol(elf, symbol):
    """Resolve a symbol with ``nm`` for direct RAM launch setup."""
    # Resolve entry/stack symbols up front so OpenOCD can start from RAM
    # directly without relying on a flash boot flow.
    return resolve_symbol_with_nm(
        elf, symbol, nm=os.environ.get("NM", "arm-none-eabi-nm")
    )


def openocd_cli():
    """Return the OpenOCD executable path, or report a helpful error."""
    openocd = find_openocd(os.environ.get("OPENOCD", ""))
    if openocd is None:
        err("OpenOCD not found; set OPENOCD or ensure openocd is on PATH")
    return openocd


def _openocd_config_cmd(openocd, elf, main_thumb, estack_addr, timeout_s, under_reset):
    """Build the OpenOCD command for one FLEXMEM configuration attempt."""
    script_lines = flexmem_script_lines(
        elf=elf,
        main_thumb=main_thumb,
        estack_addr=estack_addr,
        timeout_ms=int(timeout_s * 1000),
        flexmem_addr=CM55TCMCR_ADDR,
        expected_mask=CM55TCMCR_EXPECTED_MASK,
        expected_value=CM55TCMCR_EXPECTED_VALUE,
        connect_under_reset=under_reset,
    )
    with tempfile.NamedTemporaryFile("w", delete=False, suffix=".cfg") as script:
        script.write("\n".join(script_lines))
        script.write("\n")
        script_path = script.name

    cmd = openocd_base_args(
        openocd=openocd,
        speed=speed_khz_from_env(),
        serial=serial_from_env(),
        transport=transport_from_env(),
    ) + ["-f", script_path]
    return cmd, script_path


def _openocd_init_failed(output):
    """Return whether OpenOCD failed before it could attach to the target."""
    lower = (output or "").lower()
    return "init mode failed" in lower or "unable to connect to the target" in lower


def _run_openocd_config_once(
    openocd, elf, main_thumb, estack_addr, timeout_s, under_reset
):
    """Run one OpenOCD FLEXMEM configuration attempt."""
    cmd, script_path = _openocd_config_cmd(
        openocd, elf, main_thumb, estack_addr, timeout_s, under_reset
    )
    try:
        cp = run_quiet(cmd)
    finally:
        try:
            os.unlink(script_path)
        except OSError:
            pass
    return cp


def run_openocd_config(elf, main_thumb, estack_addr, timeout_s):
    """Download and run the config ELF using OpenOCD."""
    openocd = openocd_cli()
    if openocd is None:
        return 2

    cp = _run_openocd_config_once(
        openocd, elf, main_thumb, estack_addr, timeout_s, under_reset=True
    )
    if cp.returncode != 0 and _openocd_init_failed(cp.stdout):
        if os.environ.get("FLEXMEM_VERBOSE"):
            log_output(cp.stdout, logging.DEBUG)
            LOG.debug(
                "OpenOCD connect-under-reset attach failed; retrying FLEXMEM "
                "configuration without connect_assert_srst"
            )
        cp = _run_openocd_config_once(
            openocd, elf, main_thumb, estack_addr, timeout_s, under_reset=False
        )
    if os.environ.get("FLEXMEM_VERBOSE") or cp.returncode != 0:
        log_output(cp.stdout, logging.DEBUG if cp.returncode == 0 else logging.ERROR)
    if cp.returncode != 0:
        err("OpenOCD FLEXMEM config RAM download/start failed")
    return cp.returncode


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

    main_addr = resolve_symbol(elf, "main")
    estack_addr = resolve_symbol(elf, "_estack")
    if main_addr is None or estack_addr is None:
        err("Failed to resolve main/_estack in config ELF")
        return 2
    main_thumb = hex(int(main_addr, 16) | 1)

    timeout_s = float(os.environ.get("FLEXMEM_CONFIG_TIMEOUT", "30"))

    return run_openocd_config(elf, main_thumb, estack_addr, timeout_s)


if __name__ == "__main__":
    raise SystemExit(main())
