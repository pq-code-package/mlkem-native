#!/usr/bin/env python3
# Copyright (c) The mldsa-native project authors
# Copyright (c) The mlkem-native project authors
# Copyright (c) Arm Ltd.
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

"""
Run one RAM-resident NUCLEO-N657X0-Q test ELF through OpenOCD.

The wrapper expects ``flexmem_configure.py`` to have expanded ITCM/DTCM before
normal runs. If the initial GDB ``load`` reports that loading failed before
target output starts, the wrapper can re-run FLEXMEM configuration and retry
the same ELF. Successful runs load the ELF into RAM, let C startup clear
memory, restore a packed argv blob at ``__wrap_main``, dump target stdout from
the RAM capture buffer, and map target sentinels to the process exit status
expected by the baremetal test harness.
"""

import logging
import os
import subprocess
import sys
import tempfile
import time
import select

from nucleo_host.argv_blob import pack_cmdline
from nucleo_host.flexmem import flexmem_config_build_instructions
from nucleo_host.gdb_script import build_run_script
from nucleo_host.openocd_tools import find_openocd
from nucleo_host.openocd_tools import runtime_gdbserver_cmd
from nucleo_host.openocd_tools import serial_from_env
from nucleo_host.openocd_tools import speed_khz_from_env
from nucleo_host.openocd_tools import transport_from_env
from nucleo_host.results import LAYOUT_FAIL_SENTINEL
from nucleo_host.results import fault_info_from_gdb
from nucleo_host.results import gdb_load_failed_before_target_output
from nucleo_host.results import gdb_observed_hardfault
from nucleo_host.results import split_stdout_capture
from nucleo_host.symbols import default_readelf
from nucleo_host.symbols import resolve_symbol

VERBOSE = False
STDOUT_BYTES_EMITTED = 0
TARGET_FAILURE = False
TARGET_FAILURE_KIND = ""
SUPPRESS_RETRYABLE_DIAGNOSTICS = False
LAST_FAULT_DIAGNOSTICS = ""
LAST_LOAD_FAILURE_DIAGNOSTICS = ""
LOG = logging.getLogger(__name__)


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


def err(msg, **kwargs):
    """Report an error message regardless of verbose mode."""
    # Always report errors, including multiline subprocess diagnostics.
    log_output(msg, logging.ERROR)


def info(msg, **kwargs):
    """Report an informational message only in verbose mode."""
    if VERBOSE:
        LOG.debug("%s", msg)


def run(cmd, **kwargs):
    """Thin wrapper around ``subprocess.run`` for test-time monkeypatching."""
    return subprocess.run(cmd, **kwargs)


def popen(cmd, **kwargs):
    """Wrap ``subprocess.Popen`` for test-time monkeypatching."""
    return subprocess.Popen(cmd, **kwargs)


def _default_flexmem_config_elf() -> str:
    """Return the default build path for the FLEXMEM configuration ELF."""
    platform_dir = os.path.dirname(os.path.abspath(__file__))
    repo_root = os.path.abspath(os.path.join(platform_dir, "..", "..", "..", ".."))
    return os.path.join(
        repo_root, "test", "build", "nucleo-n657x0-q", "flexmem_config.elf"
    )


def _recover_flexmem(reason: str, failure_message: str) -> bool:
    """Re-run FLEXMEM after a retryable setup or target failure."""
    platform_dir = os.path.dirname(os.path.abspath(__file__))
    configure_script = os.path.join(platform_dir, "flexmem_configure.py")
    config_elf = os.environ.get("FLEXMEM_CONFIG_ELF", _default_flexmem_config_elf())

    if not os.path.exists(configure_script):
        err(f"FLEXMEM configure script not found: {configure_script}")
        return False
    if not os.path.exists(config_elf):
        err(f"FLEXMEM config ELF not found: {config_elf}")
        err(flexmem_config_build_instructions(config_elf))
        return False

    info(f"[exec_wrapper] recovering from {reason}: re-running FLEXMEM config")
    recovery_env = os.environ.copy()
    cp = run(
        [sys.executable, configure_script, config_elf],
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True,
        env=recovery_env,
    )
    if cp.returncode != 0:
        err(failure_message)
        log_output(cp.stdout, logging.ERROR)
        return False
    if VERBOSE:
        log_output(cp.stdout, logging.DEBUG)
    return True


def _recover_after_hardfault() -> bool:
    """Re-run FLEXMEM configuration after a target HardFault retry trigger."""
    return _recover_flexmem(
        "HardFault", "FLEXMEM reconfiguration after HardFault failed"
    )


def _recover_after_load_failure() -> bool:
    """Re-run FLEXMEM configuration after a GDB load failure retry trigger."""
    return _recover_flexmem(
        "GDB load failure",
        "FLEXMEM reconfiguration after GDB load failure failed",
    )


def _run_once():
    """Run the target ELF once and return its wrapper exit code."""
    global VERBOSE
    global STDOUT_BYTES_EMITTED
    global TARGET_FAILURE
    global TARGET_FAILURE_KIND
    global SUPPRESS_RETRYABLE_DIAGNOSTICS
    global LAST_FAULT_DIAGNOSTICS
    global LAST_LOAD_FAILURE_DIAGNOSTICS

    STDOUT_BYTES_EMITTED = 0
    TARGET_FAILURE = False
    TARGET_FAILURE_KIND = ""
    LAST_FAULT_DIAGNOSTICS = ""
    LAST_LOAD_FAILURE_DIAGNOSTICS = ""

    argv = sys.argv[1:]
    # Minimal flag parsing for wrapper flags (remove them from argv)
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
    args = argv  # keep same convention as M55 wrapper: argv[0] is binpath

    if not os.path.exists(elf):
        err(f"ELF not found: {elf}")
        return 2

    gdb = os.environ.get("GDB", "arm-none-eabi-gdb")
    nm = os.environ.get("NM", "arm-none-eabi-nm")
    readelf = os.environ.get("READELF", default_readelf())
    port = int(os.environ.get("GDB_PORT", "3333"))
    gdb_run_timeout = float(os.environ.get("GDB_RUN_TIMEOUT", "180"))

    # Address extraction for argv block symbol. Numeric addresses avoid
    # debugger symbol issues.
    arg_block_sym = os.environ.get("ARG_BLOCK_SYMBOL", "mlkem_cmdline_block")
    arg_block_addr = None

    def _resolve_symbol_addr(elf_path: str, sym: str):
        """Resolve a symbol with the wrapper-selected binary utilities."""
        return resolve_symbol(elf_path, sym, nm=nm, readelf=readelf)

    # Try both expected names in case of historical rename
    for cand in (arg_block_sym, "mlk_cmdline_block"):
        addr = _resolve_symbol_addr(elf, cand)
        if addr is not None:
            arg_block_sym = cand
            arg_block_addr = addr
            break

    # Numeric breakpoints avoid GDB symbol lookup surprises after loading
    # RAM ELFs.
    wrap_main_addr = _resolve_symbol_addr(elf, "__wrap_main")
    wrap_main_break = "__wrap_main"
    if wrap_main_addr is not None:
        wrap_main_break = f"*{wrap_main_addr}"
    reset_handler_addr = _resolve_symbol_addr(elf, "Reset_Handler")
    reset_handler_jump = "Reset_Handler"
    if reset_handler_addr is not None:
        reset_handler_jump = f"*{hex(int(reset_handler_addr, 16) | 1)}"
    if reset_handler_addr is None:
        err("Failed to resolve Reset_Handler in ELF.")
        return 2

    # Resolve the RAM stdout buffer so GDB can dump target output after
    # execution.
    stdout_capture_addr = _resolve_symbol_addr(elf, "nucleo_stdout_capture")
    stdout_capture_len_addr = _resolve_symbol_addr(elf, "nucleo_stdout_capture_len")
    stdout_capture_truncated_addr = _resolve_symbol_addr(
        elf, "nucleo_stdout_capture_truncated"
    )
    stdout_capture_size = int(
        os.environ.get("NUCLEO_STDOUT_CAPTURE_SIZE", str(1536 * 1024))
    )
    # Allow override of base address via env (hex string)
    arg_block_addr_env = os.environ.get("ARG_BLOCK_ADDR")
    base_addr = None
    if arg_block_addr_env:
        try:
            base_addr = int(arg_block_addr_env, 16)
        except Exception:
            base_addr = None
    if base_addr is None and arg_block_addr:
        try:
            base_addr = int(arg_block_addr, 16)
        except Exception:
            base_addr = None

    if base_addr is None:
        err(
            "Failed to resolve base address of argv block "
            "(mlkem_cmdline_block/mlk_cmdline_block)."
        )
        err(
            "- Ensure symbols are present in ELF, or set ARG_BLOCK_ADDR to "
            "the base address (hex)."
        )
        return 2

    try:
        blob = pack_cmdline(args, base_addr)
    except ValueError as exc:
        err(str(exc))
        return 2

    with tempfile.TemporaryDirectory() as td:
        argv_bin = os.path.join(td, "argv.bin")
        with open(argv_bin, "wb") as f:
            f.write(blob)
        # GDB writes target stdout here after the run; Python logs it below.
        stdout_capture_bin = os.path.join(td, "stdout-capture.bin")
        openocd = find_openocd(os.environ.get("OPENOCD", ""))
        if openocd is None:
            err("OpenOCD not found; set OPENOCD or ensure openocd is on PATH")
            return 2
        gdbserver_cmd = runtime_gdbserver_cmd(
            openocd=openocd,
            port=port,
            speed=speed_khz_from_env(),
            serial=serial_from_env(),
            transport=transport_from_env(),
        )
        server_label = "OpenOCD"

        info(
            "[exec_wrapper] assuming FLEXMEM was configured by "
            "flexmem_configure.py; no runtime TCM probing"
        )

        info(f"[exec_wrapper] starting {server_label} on port {port}...")
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
            exit_code = None
            time.sleep(0.8)

            # Give the server a brief moment, then check for early exit
            if stp.poll() is not None:
                # Server exited early: surface its output as the setup failure.
                out_rem = stp.stdout.read() if stp.stdout else ""
                if out_rem and not SUPPRESS_RETRYABLE_DIAGNOSTICS:
                    log_output(out_rem, logging.DEBUG if VERBOSE else logging.ERROR)
                return 2

            gdb_lines = build_run_script(
                port=port,
                wrap_main_break=wrap_main_break,
                reset_handler_jump=reset_handler_jump,
                argv_bin=argv_bin,
                arg_block_addr=arg_block_addr,
                arg_block_sym=arg_block_sym,
                stdout_capture_addr=stdout_capture_addr,
                stdout_capture_len_addr=stdout_capture_len_addr,
                stdout_capture_truncated_addr=stdout_capture_truncated_addr,
                stdout_capture_size=stdout_capture_size,
                stdout_capture_bin=stdout_capture_bin,
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

            # Run GDB while draining OpenOCD output so probe diagnostics are
            # available in verbose mode without blocking the wrapper.
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

            # Stream OpenOCD output until gdb finishes without blocking on
            # readline().
            while True:
                if stp.stdout is not None:
                    try:
                        r, _, _ = select.select([stp.stdout], [], [], 0.1)
                        if r:
                            line = stp.stdout.readline()
                            if line:
                                # OpenOCD stdout is logged only in verbose
                                # mode.
                                if VERBOSE:
                                    log_output(line, logging.DEBUG)
                    except Exception:
                        # If select/readline fails, avoid blocking the loop
                        pass
                # Check if gdb has completed
                if gdbp.poll() is not None:
                    break
                if gdb_deadline is not None and time.time() > gdb_deadline:
                    if not SUPPRESS_RETRYABLE_DIAGNOSTICS:
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
                        if out and not SUPPRESS_RETRYABLE_DIAGNOSTICS:
                            log_output(out, logging.ERROR)
                        if errout and not SUPPRESS_RETRYABLE_DIAGNOSTICS:
                            err(errout, end="")
                    except Exception:
                        pass
                    return 124

            out, errout = gdbp.communicate()
            if out and VERBOSE:
                log_output(out, logging.DEBUG)
            if errout and VERBOSE:
                # gdb chatter / errors (verbose only)
                err(errout, end="")

            gdb_text = f"{out}\n{errout}"
            layout_failed = LAYOUT_FAIL_SENTINEL in gdb_text
            hardfaulted = gdb_observed_hardfault(gdb_text)
            target_failed = layout_failed or hardfaulted

            if os.path.exists(stdout_capture_bin):
                try:
                    # Parse the same exit sentinel from dumped RAM output as
                    # the target prints before stopping at the completion trap.
                    with open(stdout_capture_bin, "rb") as capture_file:
                        captured = capture_file.read()
                    captured_output, captured_exit_code = split_stdout_capture(captured)
                    if captured_exit_code is not None:
                        exit_code = captured_exit_code
                    if captured_output and not target_failed:
                        sys.stdout.write(captured_output)
                        sys.stdout.flush()
                        STDOUT_BYTES_EMITTED += len(captured_output.encode("utf-8"))
                except Exception as exc:
                    info(f"[exec_wrapper] failed to read stdout capture: {exc}")

            if "$nucleo_stdout_truncated = 0x1" in gdb_text:
                err("WARNING: target stdout capture truncated")

            if exit_code is not None:
                return int(exit_code) if isinstance(exit_code, int) else 1

            if layout_failed:
                TARGET_FAILURE = True
                TARGET_FAILURE_KIND = "layout"
                err("FAIL!")
                err("FLEXMEM layout check failed on target")
                return 1

            if hardfaulted:
                TARGET_FAILURE = True
                TARGET_FAILURE_KIND = "hardfault"
                fault_info = fault_info_from_gdb(gdb_text)
                LAST_FAULT_DIAGNOSTICS = fault_info
                if not SUPPRESS_RETRYABLE_DIAGNOSTICS:
                    err("FAIL!")
                    err("Target entered HardFault_Handler")
                    if fault_info:
                        err(fault_info)
                return 1

            if "Program received signal SIGTRAP" in gdb_text:
                if stdout_capture_addr and stdout_capture_len_addr:
                    TARGET_FAILURE = True
                    TARGET_FAILURE_KIND = "missing-exit-sentinel"
                    if not SUPPRESS_RETRYABLE_DIAGNOSTICS:
                        err("FAIL!")
                        err("target stopped at SIGTRAP without ML-KEM exit sentinel")
                    return 1
                info("[exec_wrapper] completion trap observed without exit sentinel")
                return 0

            if gdbp.returncode != 0:
                target_output_observed = STDOUT_BYTES_EMITTED != 0
                exit_code_observed = exit_code is not None
                if gdb_load_failed_before_target_output(
                    gdb_text,
                    target_output_observed=target_output_observed,
                    exit_code_observed=exit_code_observed,
                ):
                    TARGET_FAILURE = True
                    TARGET_FAILURE_KIND = "load-failed"
                    LAST_LOAD_FAILURE_DIAGNOSTICS = gdb_text
                    return gdbp.returncode
                if not SUPPRESS_RETRYABLE_DIAGNOSTICS:
                    err("FAIL!")
                    err(f"gdb batch failed with code {gdbp.returncode}")
                if out and not SUPPRESS_RETRYABLE_DIAGNOSTICS:
                    log_output(out, logging.ERROR)
                if errout and not SUPPRESS_RETRYABLE_DIAGNOSTICS:
                    log_output(errout, logging.ERROR)
                return gdbp.returncode

            return 0

        finally:
            # Terminate OpenOCD.
            try:
                stp.terminate()
                stp.wait(timeout=1.5)
            except Exception:
                try:
                    stp.kill()
                except Exception:
                    pass
            # Remove the temp gdb script
            try:
                if "gdb_script_path" in locals():
                    os.unlink(gdb_script_path)
            except Exception:
                pass


def main():
    """Run the wrapper with configured transport and FLEXMEM retry policy."""
    global SUPPRESS_RETRYABLE_DIAGNOSTICS
    global LAST_FAULT_DIAGNOSTICS

    attempts = max(1, int(os.environ.get("GDB_RUN_ATTEMPTS", "2")))
    hardfault_attempts = max(
        0, int(os.environ.get("GDB_HARDFAULT_RECOVERY_ATTEMPTS", "1"))
    )
    load_failure_attempts = max(
        0, int(os.environ.get("GDB_LOAD_FAILURE_RECOVERY_ATTEMPTS", "1"))
    )
    transport_retries = 0
    hardfault_recoveries = 0
    load_failure_recoveries = 0
    last_rc = 1

    while True:
        can_retry_transport = transport_retries < attempts - 1
        can_retry_hardfault = hardfault_recoveries < hardfault_attempts
        can_retry_load_failure = load_failure_recoveries < load_failure_attempts
        SUPPRESS_RETRYABLE_DIAGNOSTICS = (
            can_retry_transport or can_retry_hardfault or can_retry_load_failure
        )
        last_rc = _run_once()
        if last_rc == 0:
            return 0
        if TARGET_FAILURE_KIND == "load-failed":
            if can_retry_load_failure:
                load_failure_recoveries += 1
                if not VERBOSE:
                    err(
                        "[exec_wrapper] GDB load failed before target output; "
                        "re-running FLEXMEM config"
                    )
                if _recover_after_load_failure():
                    if VERBOSE:
                        err(
                            "[exec_wrapper] retrying after recovered GDB "
                            "load failure "
                            f"({load_failure_recoveries}/"
                            f"{load_failure_attempts})"
                        )
                    time.sleep(0.5)
                    continue
                if LAST_LOAD_FAILURE_DIAGNOSTICS:
                    err("GDB load-failure diagnostics from failed run:")
                    err(LAST_LOAD_FAILURE_DIAGNOSTICS)
                return last_rc
            err("FAIL!")
            err(
                "GDB load failed before target output and FLEXMEM recovery "
                "attempts are exhausted"
            )
            err(f"gdb batch failed with code {last_rc}")
            if LAST_LOAD_FAILURE_DIAGNOSTICS:
                log_output(LAST_LOAD_FAILURE_DIAGNOSTICS, logging.ERROR)
            return last_rc
        if TARGET_FAILURE_KIND == "hardfault" and can_retry_hardfault:
            hardfault_recoveries += 1
            if _recover_after_hardfault():
                if VERBOSE:
                    err(
                        "[exec_wrapper] retrying after recovered "
                        "HardFault "
                        f"({hardfault_recoveries}/"
                        f"{hardfault_attempts})"
                    )
                time.sleep(0.5)
                continue
            if LAST_FAULT_DIAGNOSTICS:
                err("HardFault diagnostics from failed run:")
                err(LAST_FAULT_DIAGNOSTICS)
            return last_rc
        if TARGET_FAILURE or STDOUT_BYTES_EMITTED != 0 or not can_retry_transport:
            return last_rc
        transport_retries += 1
        if VERBOSE:
            err(
                "[exec_wrapper] retrying after transport failure "
                f"({transport_retries}/{attempts - 1})"
            )
        time.sleep(0.5)


if __name__ == "__main__":
    raise SystemExit(main())
