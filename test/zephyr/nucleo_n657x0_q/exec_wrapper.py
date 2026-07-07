#!/usr/bin/env python3
# Copyright (c) The mldsa-native project authors
# Copyright (c) The mlkem-native project authors
# Copyright (c) Arm Ltd.
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

"""
Run one RAM-resident NUCLEO-N657X0-Q Zephyr test ELF through OpenOCD.

The wrapper first expands ITCM/DTCM with the direct FLEXMEM OpenOCD script. It
then starts OpenOCD with SWO trace redirected to a local TCP listener,
GDB-loads the Zephyr ELF into RAM, restores a dynamic bootargs string after
Zephyr startup reaches ``get_bootargs``, decodes target stdout from ITM port 0,
and reads the target return code from ``r0`` at the ``nucleo_test_done``
breakpoint.
"""

import logging
import os
import re
import select
import socket
import subprocess
import sys
import tempfile
import time

from nucleo_host.flexmem_configure import run_openocd_config as run_flexmem_config
from nucleo_host.gdb_script import build_run_script
from nucleo_host.openocd_tools import find_openocd
from nucleo_host.openocd_tools import runtime_gdbserver_cmd
from nucleo_host.openocd_tools import serial_from_env
from nucleo_host.openocd_tools import speed_khz_from_env
from nucleo_host.openocd_tools import swo_formatter_from_env
from nucleo_host.openocd_tools import swo_pin_freq_from_env
from nucleo_host.openocd_tools import swo_traceclk_from_env
from nucleo_host.openocd_tools import transport_from_env
from nucleo_host.results import fault_info_from_gdb
from nucleo_host.results import gdb_observed_hardfault
from nucleo_host.symbols import default_readelf
from nucleo_host.symbols import resolve_symbol

VERBOSE = False
LOG = logging.getLogger(__name__)
BOOTARGS_BLOCK_SIZE = 64 * 1024


def _quote_bootarg(arg):
    """
    Quote one argument for Zephyr's boot_args.c parser.

    Zephyr groups a token when it starts with a matching single or double quote,
    and strips the quote characters. It does not implement shell-style escapes.
    """
    if arg == "" or arg[0] in ("'", '"') or any(ch.isspace() for ch in arg):
        if "'" not in arg:
            return f"'{arg}'"
        if '"' not in arg:
            return f'"{arg}"'
        raise ValueError(
            "Zephyr bootargs cannot represent arguments that need quoting "
            "and contain both quote characters"
        )
    return arg


def _pack_bootargs(args, block_size=BOOTARGS_BLOCK_SIZE):
    """
    Return a padded UTF-8 dynamic bootargs command line for Zephyr.

    The NUCLEO runner restores this string into the fixed target reservation
    before Zephyr calls ``get_bootargs()``. The result is padded to the full
    reservation so GDB ``restore`` overwrites stale contents from prior runs.
    """
    cmdline = " ".join(_quote_bootarg(arg) for arg in args).encode("utf-8") + b"\x00"
    if len(cmdline) > block_size:
        raise ValueError(
            f"bootargs string is {len(cmdline)} bytes, exceeds {block_size}-byte block"
        )
    return cmdline + bytes(block_size - len(cmdline))


def configure_logging():
    """Configure process-wide logging after ``VERBOSE`` has been parsed."""
    level = logging.DEBUG if VERBOSE else logging.INFO
    logging.basicConfig(level=level, format="%(message)s")


def log_output(output, level=logging.INFO, prefix=None):
    """Log multiline subprocess output one line at a time."""
    if not output:
        return
    for line in str(output).rstrip().splitlines():
        if prefix:
            line = f"{prefix}{line}"
        LOG.log(level, "%s", line)


def err(msg):
    """Report an error message regardless of verbose mode."""
    log_output(msg, logging.ERROR)


def info(msg):
    """Report an informational message only in verbose mode."""
    if VERBOSE:
        LOG.debug("%s", msg)


def popen(cmd, **kwargs):
    """Wrap ``subprocess.Popen`` for test-time monkeypatching."""
    return subprocess.Popen(cmd, **kwargs)


def _reserve_localhost_port():
    """Return an available localhost TCP port for OpenOCD to listen on."""
    with socket.socket(socket.AF_INET, socket.SOCK_STREAM) as sock:
        sock.bind(("127.0.0.1", 0))
        return sock.getsockname()[1]


def _emit_target_bytes(data: bytes):
    """Forward decoded target stdout/stderr bytes to host stdout."""
    if not data:
        return
    out = getattr(sys.stdout, "buffer", None)
    if out is not None:
        out.write(data)
        out.flush()
    else:
        sys.stdout.write(data.decode("utf-8", errors="replace"))
        sys.stdout.flush()


def _decode_swo_itm(state, data: bytes):
    """Extract software stimulus port 0 bytes from raw ITM trace packets."""
    out = bytearray()
    remaining = state.get("itm_remaining", 0)
    emit = state.get("itm_emit", False)

    for byte in data:
        if remaining:
            if emit:
                out.append(byte)
            remaining -= 1
            continue

        size_code = byte & 0x03
        if size_code == 0:
            continue

        remaining = 4 if size_code == 3 else size_code
        port = (byte >> 3) & 0x1F
        is_software_packet = (byte & 0x04) == 0
        emit = is_software_packet and port == 0

    state["itm_remaining"] = remaining
    state["itm_emit"] = emit
    return bytes(out)


def _drain_swo(state):
    """Connect to and drain OpenOCD SWO TCP output without blocking."""
    conn = state.get("conn")
    if conn is None:
        try:
            conn = socket.create_connection(("127.0.0.1", state["port"]), timeout=0.01)
            conn.setblocking(False)
            state["conn"] = conn
        except OSError:
            return

    conn = state.get("conn")
    if conn is None:
        return

    while True:
        try:
            readable, _, _ = select.select([conn], [], [], 0)
            if not readable:
                return
            data = conn.recv(4096)
        except OSError:
            state["conn"] = None
            return
        if not data:
            try:
                conn.close()
            except OSError:
                pass
            state["conn"] = None
            return
        decoded = _decode_swo_itm(state, data)
        state["swo_raw_bytes"] = state.get("swo_raw_bytes", 0) + len(data)
        _emit_target_bytes(decoded)


def _wait_swo_connected(state, timeout_s=3.0):
    """Connect to OpenOCD's SWO TCP listener before target execution."""
    deadline = time.time() + timeout_s
    while time.time() < deadline:
        _drain_swo(state)
        if state.get("conn") is not None:
            return True
        time.sleep(0.05)
    return False


def _close_swo_state(state):
    """Close SWO connection handles."""
    conn = state.get("conn")
    if conn is not None:
        try:
            conn.close()
        except OSError:
            pass


def _drain_swo_until_idle(state, idle_s=0.5, timeout_s=5.0):
    """Drain delayed SWO bytes until the stream is briefly idle."""
    deadline = time.time() + timeout_s
    idle_deadline = time.time() + idle_s
    last_raw_bytes = state.get("swo_raw_bytes", 0)

    while time.time() < deadline:
        _drain_swo(state)
        raw_bytes = state.get("swo_raw_bytes", 0)
        if raw_bytes != last_raw_bytes:
            last_raw_bytes = raw_bytes
            idle_deadline = time.time() + idle_s
        elif time.time() >= idle_deadline:
            break
        time.sleep(0.01)


def _parse_exit_code(gdb_text: str):
    """Return the target exit code printed by the GDB script, if present."""
    match = re.search(r"^NUCLEO_EXIT_CODE=(-?\d+)$", gdb_text, re.MULTILINE)
    if match:
        return int(match.group(1))
    return None


def _run_once():
    """Run the target ELF once and return its wrapper exit code."""
    global VERBOSE

    argv = sys.argv[1:]
    if "--verbose" in argv:
        VERBOSE = True
        argv.remove("--verbose")
    if "-v" in argv:
        VERBOSE = True
        argv.remove("-v")

    configure_logging()

    if len(argv) < 1:
        err("Usage: exec_wrapper.py [--verbose] <ELF> [args...]")
        return 2

    elf = os.path.abspath(argv[0])
    args = argv  # Preserve the existing convention: argv[0] is the ELF path.

    if not os.path.exists(elf):
        err(f"ELF not found: {elf}")
        return 2

    gdb = os.environ.get("GDB", "arm-none-eabi-gdb")
    nm = os.environ.get("NM", "arm-none-eabi-nm")
    readelf = os.environ.get("READELF", default_readelf())
    port = int(os.environ.get("GDB_PORT", "3333"))
    gdb_run_timeout = float(os.environ.get("GDB_RUN_TIMEOUT", "180"))

    arg_block_sym = "mlk_bootargs_block"
    arg_block_addr = None

    def _resolve_symbol_addr(elf_path: str, sym: str):
        return resolve_symbol(elf_path, sym, nm=nm, readelf=readelf)

    def _resolve_first_symbol(elf_path: str, symbols):
        for sym in symbols:
            addr = _resolve_symbol_addr(elf_path, sym)
            if addr is not None:
                return sym, addr
        return symbols[0], None

    for cand in (arg_block_sym, "mlkem_bootargs_block"):
        addr = _resolve_symbol_addr(elf, cand)
        if addr is not None:
            arg_block_sym = cand
            arg_block_addr = addr
            break

    bootargs_sym, bootargs_addr = _resolve_first_symbol(elf, ["get_bootargs"])
    bootargs_break = bootargs_sym
    if bootargs_addr is not None:
        bootargs_break = f"*{bootargs_addr}"

    done_sym, done_addr = _resolve_first_symbol(
        elf, ["nucleo_test_breakpoint", "nucleo_test_done"]
    )
    done_break = done_sym
    if done_addr is not None:
        done_break = f"*{done_addr}"

    hardfault_sym, hardfault_addr = _resolve_first_symbol(
        elf, ["HardFault_Handler", "z_arm_hard_fault"]
    )
    hardfault_break = hardfault_sym
    if hardfault_addr is not None:
        hardfault_break = f"*{hardfault_addr}"

    reset_handler_sym, reset_handler_addr = _resolve_first_symbol(
        elf, ["Reset_Handler", "z_arm_reset"]
    )
    reset_handler_jump = reset_handler_sym
    if reset_handler_addr is not None:
        reset_handler_jump = f"*{hex(int(reset_handler_addr, 16) | 1)}"
    if reset_handler_addr is None:
        err("Failed to resolve Reset_Handler/z_arm_reset in ELF.")
        return 2

    base_addr = None
    if arg_block_addr:
        try:
            base_addr = int(arg_block_addr, 16)
        except ValueError:
            base_addr = None

    if base_addr is None:
        err(
            "Failed to resolve base address of bootargs block "
            "(mlk_bootargs_block/mlkem_bootargs_block)."
        )
        err("- Ensure symbols are present in ELF.")
        return 2

    try:
        blob = _pack_bootargs(args)
    except ValueError as exc:
        err(str(exc))
        return 2

    with tempfile.TemporaryDirectory() as td:
        argv_bin = os.path.join(td, "argv.bin")
        with open(argv_bin, "wb") as f:
            f.write(blob)

        flexmem_timeout_s = float(os.environ.get("FLEXMEM_CONFIG_TIMEOUT", "5"))
        info("[exec_wrapper] configuring FLEXMEM...")
        flexmem_rc = run_flexmem_config(flexmem_timeout_s)
        if flexmem_rc != 0:
            return flexmem_rc

        swo_port = _reserve_localhost_port()
        swo_state = {"conn": None, "port": swo_port}
        openocd = find_openocd(os.environ.get("OPENOCD", ""))
        if openocd is None:
            _close_swo_state(swo_state)
            err("OpenOCD not found; set OPENOCD or ensure openocd is on PATH")
            return 2
        gdbserver_cmd = runtime_gdbserver_cmd(
            openocd=openocd,
            port=port,
            swo_port=swo_port,
            swo_traceclk=swo_traceclk_from_env(),
            swo_pin_freq=swo_pin_freq_from_env(),
            swo_formatter=swo_formatter_from_env(),
            speed=speed_khz_from_env(),
            serial=serial_from_env(),
            transport=transport_from_env(),
        )

        info(f"[exec_wrapper] starting OpenOCD on port {port}...")
        info(f"[exec_wrapper] SWO redirect port {swo_port}")
        info(f"[exec_wrapper] {' '.join(gdbserver_cmd)}")
        stp = popen(
            gdbserver_cmd,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            text=True,
            bufsize=1,
            universal_newlines=True,
        )

        try:
            time.sleep(0.8)

            if stp.poll() is not None:
                out_rem = stp.stdout.read() if stp.stdout else ""
                if out_rem:
                    log_output(out_rem, logging.DEBUG if VERBOSE else logging.ERROR)
                return 2
            if not _wait_swo_connected(swo_state):
                err("FAIL!")
                err("failed to connect to OpenOCD SWO TCP listener")
                return 2

            gdb_lines = build_run_script(
                port=port,
                bootargs_break=bootargs_break,
                reset_handler_jump=reset_handler_jump,
                hardfault_break=hardfault_break,
                done_break=done_break,
                argv_bin=argv_bin,
                arg_block_addr=arg_block_addr,
                arg_block_sym=arg_block_sym,
            )

            if VERBOSE:
                LOG.debug("============ GDB SCRIPT ============")
                log_output("\n".join(gdb_lines), logging.DEBUG)
                LOG.debug("====================================")

            with tempfile.NamedTemporaryFile("w", delete=False, suffix=".gdb") as gs:
                for line in gdb_lines:
                    gs.write(line + "\n")
                gdb_script_path = gs.name

            gdb_cmd = [gdb, "--batch", "-x", gdb_script_path, elf]

            info("[exec_wrapper] running gdb batch")
            gdbp = popen(
                gdb_cmd,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                text=True,
            )
            gdb_deadline = (
                time.time() + gdb_run_timeout if gdb_run_timeout > 0 else None
            )

            while True:
                _drain_swo(swo_state)
                if stp.stdout is not None:
                    try:
                        r, _, _ = select.select([stp.stdout], [], [], 0.1)
                        if r:
                            line = stp.stdout.readline()
                            if line and VERBOSE:
                                log_output(line, logging.DEBUG)
                    except Exception:
                        pass
                if gdbp.poll() is not None:
                    break
                if gdb_deadline is not None and time.time() > gdb_deadline:
                    err("FAIL!")
                    err(f"gdb batch timed out after {gdb_run_timeout:.0f}s")
                    try:
                        gdbp.terminate()
                        gdbp.wait(timeout=1.0)
                    except Exception:
                        try:
                            gdbp.kill()
                        except Exception:
                            pass
                    try:
                        out, errout = gdbp.communicate(timeout=1.0)
                        if out:
                            log_output(out, logging.ERROR)
                        if errout:
                            log_output(errout, logging.ERROR)
                    except Exception:
                        pass
                    return 124

            out, errout = gdbp.communicate()
            _drain_swo_until_idle(swo_state)
            if out and VERBOSE:
                log_output(out, logging.DEBUG)
            if errout and VERBOSE:
                log_output(errout, logging.DEBUG)

            gdb_text = f"{out}\n{errout}"
            exit_code = _parse_exit_code(gdb_text)
            hardfaulted = gdb_observed_hardfault(gdb_text)

            if exit_code is not None:
                return exit_code

            if hardfaulted:
                fault_info = fault_info_from_gdb(gdb_text)
                err("FAIL!")
                err("Target entered HardFault_Handler")
                if fault_info:
                    err(fault_info)
                return 1

            if gdbp.returncode != 0:
                err("FAIL!")
                err(f"gdb batch failed with code {gdbp.returncode}")
                if out:
                    log_output(out, logging.ERROR)
                if errout:
                    log_output(errout, logging.ERROR)
                return gdbp.returncode

            err("FAIL!")
            err("target did not hit nucleo_test_done")
            return 1

        finally:
            try:
                stp.terminate()
                stp.wait(timeout=1.5)
            except Exception:
                try:
                    stp.kill()
                except Exception:
                    pass
            _close_swo_state(swo_state)
            try:
                if "gdb_script_path" in locals():
                    os.unlink(gdb_script_path)
            except Exception:
                pass


def main():
    """Run the wrapper once with the configured debugger transport."""
    return _run_once()


if __name__ == "__main__":
    raise SystemExit(main())
