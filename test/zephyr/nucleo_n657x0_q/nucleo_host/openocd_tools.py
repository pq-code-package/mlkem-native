# Copyright (c) The mlkem-native project authors
# Copyright (c) Arm Ltd.
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

"""Locate OpenOCD and build NUCLEO-N657X0-Q command lines."""

import os
import shutil
import subprocess


DEFAULT_INTERFACE = "interface/stlink.cfg"
DEFAULT_TARGET = "target/stm32n6x.cfg"
DEFAULT_CPU_TARGET = "stm32n6x.cpu"
DEFAULT_SWO_TARGET = "stm32n6x.swo"
DEFAULT_TPIU_TARGET = ""


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


def speed_khz_from_env(default="8000"):
    """Return adapter speed in kHz."""
    return os.environ.get("OPENOCD_SPEED", default)


def swo_traceclk_from_env(default="100000000"):
    """Return the target trace clock in Hz for SWO capture."""
    return os.environ.get("SWO_TRACECLK", default)


def swo_pin_freq_from_env(default="1000000"):
    """Return the async SWO pin bitrate in Hz."""
    return os.environ.get("SWO_PIN_FREQ", default)


def swo_formatter_from_env(default="0"):
    """Return the OpenOCD TPIU formatter setting for SWO capture."""
    return os.environ.get("SWO_FORMATTER", default)


def swo_target_from_env(default=DEFAULT_SWO_TARGET):
    """Return the OpenOCD trace component used for SWO capture."""
    return os.environ.get("OPENOCD_SWO_TARGET", default)


def tpiu_target_from_env(default=DEFAULT_TPIU_TARGET):
    """Return the OpenOCD TPIU component used to configure target trace output."""
    return os.environ.get("OPENOCD_TPIU_TARGET", default)


def serial_from_env(default=""):
    """Return the optional OpenOCD adapter serial selector."""
    return os.environ.get("OPENOCD_SERIAL", default)


def transport_from_env(default="swd"):
    """Return the OpenOCD transport name."""
    return os.environ.get("OPENOCD_TRANSPORT", default).strip().lower()


def run_quiet(cmd):
    """Run a command with stdout and stderr merged for delayed diagnostics."""
    return subprocess.run(
        cmd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True
    )


def openocd_base_args(
    *,
    openocd="openocd",
    interface=None,
    target=None,
    speed="8000",
    serial="",
    transport="swd",
):
    """Return common OpenOCD arguments for the NUCLEO debug connection."""
    args = [
        openocd,
        "-f",
        interface or os.environ.get("OPENOCD_INTERFACE", DEFAULT_INTERFACE),
        "-c",
        f"transport select {transport}",
        "-f",
        target or os.environ.get("OPENOCD_TARGET", DEFAULT_TARGET),
        "-c",
        (
            f"if {{[lsearch -exact [target names] {DEFAULT_CPU_TARGET}] >= 0}} "
            f"{{ {DEFAULT_CPU_TARGET} configure -defer-examine }}"
        ),
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
    swo_port=None,
    swo_traceclk="100000000",
    swo_pin_freq="1000000",
    swo_formatter="0",
    swo_target=None,
    tpiu_target=None,
    speed="8000",
    serial="",
    transport="swd",
):
    """Return the OpenOCD command used as the runtime GDB server."""
    cmd = openocd_base_args(
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
        f"{DEFAULT_CPU_TARGET} arp_examine",
    ]
    if swo_port is not None:
        swo_target = swo_target or swo_target_from_env()
        tpiu_target = tpiu_target or tpiu_target_from_env()
        if tpiu_target:
            cmd += [
                "-c",
                (
                    f"{tpiu_target} configure -protocol uart "
                    f"-traceclk {swo_traceclk} -pin-freq {swo_pin_freq} "
                    f"-formatter {swo_formatter}"
                ),
                "-c",
                f"{tpiu_target} enable",
            ]
        cmd += [
            "-c",
            (
                f"{swo_target} configure -protocol uart "
                f"-traceclk {swo_traceclk} -pin-freq {swo_pin_freq} "
                f"-output :{swo_port} -formatter {swo_formatter}"
            ),
            "-c",
            f"{swo_target} enable",
            "-c",
            f"{DEFAULT_CPU_TARGET} itm port 0 on",
        ]
    return cmd


def flexmem_script_lines(
    *,
    timeout_ms,
    mem_target=DEFAULT_CPU_TARGET,
    rcc_apb4ensr2_addr="0x56028a78",
    cm55tcmcr_addr="0x56008008",
    cm55rstcr_addr="0x56008018",
    expected_mask=0xFF,
    expected_value=0x99,
):
    """Return an OpenOCD TCL script for configuring STM32N6 FLEXMEM."""
    return [
        "reset_config none",
        "init",
        f"{mem_target} arp_examine",
        "proc read32 {addr} {",
        f"  return [lindex [{mem_target} read_memory $addr 32 1] 0]",
        "}",
        "proc write32 {addr value} {",
        f"  {mem_target} mww $addr $value",
        "}",
        f"set rcc_apb4ensr2 [read32 {rcc_apb4ensr2_addr}]",
        f"write32 {rcc_apb4ensr2_addr} [expr {{$rcc_apb4ensr2 | 0x1}}]",
        f"set cm55tcmcr [read32 {cm55tcmcr_addr}]",
        f"write32 {cm55tcmcr_addr} [expr {{($cm55tcmcr & ~0xff) | 0x{expected_value:x}}}]",
        f"set cm55rstcr [read32 {cm55rstcr_addr}]",
        f"write32 {cm55rstcr_addr} [expr {{$cm55rstcr | 0x1}}]",
        "proc wait_flexmem_configured {} {",
        f"  set deadline [expr {{[clock milliseconds] + {int(timeout_ms)}}}]",
        "  while {[clock milliseconds] < $deadline} {",
        f"    set value [read32 {cm55tcmcr_addr}]",
        f"    if {{($value & 0x{expected_mask:x}) == 0x{expected_value:x}}} {{ return }}",
        "    sleep 200",
        "  }",
        f'  error "FLEXMEM configuration register did not reach expected 0x{expected_value:x} value"',
        "}",
        "wait_flexmem_configured",
        "reset_config none",
        "reset run",
        "shutdown",
    ]
