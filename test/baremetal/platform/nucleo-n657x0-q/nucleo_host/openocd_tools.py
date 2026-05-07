# Copyright (c) The mlkem-native project authors
# Copyright (c) Arm Ltd.
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

"""Locate OpenOCD and build NUCLEO-N657X0-Q command lines."""

import os
import shutil


DEFAULT_INTERFACE = "interface/stlink.cfg"
DEFAULT_TARGET = "target/stm32n6x.cfg"


def find_openocd(openocd=""):
    """Find ``openocd`` from an explicit path or ``PATH``."""
    candidates = []
    if openocd:
        candidates.append(openocd)
    path_candidate = shutil.which("openocd")
    if path_candidate:
        candidates.append(path_candidate)
    for candidate in candidates:
        if candidate and os.path.isfile(candidate) and os.access(candidate, os.X_OK):
            return candidate
    return None


def speed_khz_from_env(default="200"):
    """Return adapter speed in kHz using the platform's existing variable."""
    return os.environ.get("OPENOCD_SPEED", os.environ.get("STLINK_SPEED", default))


def openocd_base_args(
    *,
    openocd="openocd",
    interface=None,
    target=None,
    speed="200",
    serial="",
    transport="swd",
):
    """Return common OpenOCD arguments for the NUCLEO ST-LINK connection."""
    args = [
        openocd,
        "-f",
        interface or os.environ.get("OPENOCD_INTERFACE", DEFAULT_INTERFACE),
        "-c",
        f"transport select {transport}",
        "-f",
        target or os.environ.get("OPENOCD_TARGET", DEFAULT_TARGET),
        "-c",
        f"adapter speed {speed}",
    ]
    if serial:
        args += ["-c", f"adapter serial {serial}"]
    return args


def runtime_gdbserver_cmd(
    *,
    openocd="openocd",
    port=3333,
    speed="200",
    serial="",
    transport="swd",
):
    """Return the OpenOCD command used as the runtime GDB server."""
    return openocd_base_args(
        openocd=openocd,
        speed=speed,
        serial=serial,
        transport=transport,
    ) + [
        "-c",
        "reset_config srst_only srst_nogate",
        "-c",
        f"gdb_port {port}",
        "-c",
        "tcl_port disabled",
        "-c",
        "telnet_port disabled",
        "-c",
        "init",
        "-c",
        "halt",
    ]


def flexmem_script_lines(
    *,
    elf,
    main_thumb,
    estack_addr,
    timeout_ms,
    flexmem_addr="0x56008008",
    expected_mask=0xFF,
    expected_value=0x99,
):
    """Return an OpenOCD TCL script for RAM-loading the FLEXMEM helper."""
    quoted_elf = "{" + elf.replace("\\", "\\\\").replace("}", "\\}") + "}"
    return [
        "reset_config srst_only srst_nogate connect_assert_srst",
        "init",
        "reset halt",
        f"load_image {quoted_elf}",
        f"reg msp {estack_addr}",
        f"reg pc {main_thumb}",
        "resume",
        "proc wait_flexmem_configured {} {",
        f"  set deadline [expr {{[clock milliseconds] + {int(timeout_ms)}}}]",
        "  while {[clock milliseconds] < $deadline} {",
        f"    set value [lindex [read_memory {flexmem_addr} 32 1] 0]",
        f"    if {{($value & 0x{expected_mask:x}) == 0x{expected_value:x}}} {{ return }}",
        "    sleep 200",
        "  }",
        f"  error \"FLEXMEM configuration register did not reach expected 0x{expected_value:x} value\"",
        "}",
        "wait_flexmem_configured",
        "reset run",
        "shutdown",
    ]
