#!/usr/bin/env python3
# Copyright (c) The mlkem-native project authors
# Copyright (c) Arm Ltd.
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

"""
Configure STM32N6 FLEXMEM before loading RAM-resident test images.

The helper writes the STM32N6 FLEXMEM control registers over SWD, polls
``SYSCFG->CM55TCMCR`` until the requested TCM split is visible, then resets the
target so the next ELF can be loaded into the expanded ITCM/DTCM layout.
"""

import logging
import os
import sys
import tempfile

from nucleo_host.openocd_tools import find_openocd
from nucleo_host.openocd_tools import flexmem_script_lines
from nucleo_host.openocd_tools import openocd_base_args
from nucleo_host.openocd_tools import run_quiet
from nucleo_host.openocd_tools import serial_from_env
from nucleo_host.openocd_tools import speed_khz_from_env
from nucleo_host.openocd_tools import transport_from_env

DONE = "FLEXMEM configuration complete; reset target and load test binary."

# Polling the register via SWD proves that the new ITCM/DTCM split latched
# before the next test binary is loaded.
RCC_APB4ENSR2_ADDR = "0x56028a78"
CM55TCMCR_ADDR = "0x56008008"
CM55RSTCR_ADDR = "0x56008018"
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


def openocd_cli():
    """Return the OpenOCD executable path, or report a helpful error."""
    openocd = find_openocd(os.environ.get("OPENOCD", ""))
    if openocd is None:
        err("OpenOCD not found; set OPENOCD or ensure openocd is on PATH")
    return openocd


def _openocd_config_cmd(openocd, timeout_s):
    """Build the OpenOCD command for one FLEXMEM configuration attempt."""
    script_lines = flexmem_script_lines(
        timeout_ms=int(timeout_s * 1000),
        rcc_apb4ensr2_addr=RCC_APB4ENSR2_ADDR,
        cm55tcmcr_addr=CM55TCMCR_ADDR,
        cm55rstcr_addr=CM55RSTCR_ADDR,
        expected_mask=CM55TCMCR_EXPECTED_MASK,
        expected_value=CM55TCMCR_EXPECTED_VALUE,
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


def _run_openocd_config_once(openocd, timeout_s):
    """Run the OpenOCD FLEXMEM configuration script."""
    cmd, script_path = _openocd_config_cmd(openocd, timeout_s)
    try:
        cp = run_quiet(cmd)
    finally:
        try:
            os.unlink(script_path)
        except OSError:
            pass
    return cp


def run_openocd_config(timeout_s):
    """Configure FLEXMEM using OpenOCD memory reads and writes."""
    openocd = openocd_cli()
    if openocd is None:
        return 2

    cp = _run_openocd_config_once(openocd, timeout_s)
    if os.environ.get("FLEXMEM_VERBOSE") or cp.returncode != 0:
        log_output(cp.stdout, logging.DEBUG if cp.returncode == 0 else logging.ERROR)
    if cp.returncode != 0:
        err("OpenOCD FLEXMEM register configuration failed")
    return cp.returncode


def main():
    """Configure FLEXMEM and verify the latched layout."""
    configure_logging()

    if len(sys.argv) != 1:
        err(f"Usage: {sys.argv[0]}")
        return 2

    timeout_s = float(os.environ.get("FLEXMEM_CONFIG_TIMEOUT", "5"))

    return run_openocd_config(timeout_s)


if __name__ == "__main__":
    raise SystemExit(main())
