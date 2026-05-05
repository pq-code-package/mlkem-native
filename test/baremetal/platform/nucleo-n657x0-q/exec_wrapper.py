#!/usr/bin/env python3
# Copyright (c) The mldsa-native project authors
# Copyright (c) The mlkem-native project authors
# Copyright (c) Arm Ltd.
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

import logging
import os
import re
import shlex
import shutil
import struct as st
import subprocess
import sys
import tempfile
import time
import select
import socket
import threading


VERBOSE = False
STDOUT_BYTES_EMITTED = 0
TARGET_FAILURE = False
TARGET_FAILURE_KIND = ""
SUPPRESS_RETRYABLE_DIAGNOSTICS = False
LAST_FAULT_DIAGNOSTICS = ""
LOG = logging.getLogger(__name__)
ARGV_BLOCK_SIZE = 64 * 1024


def configure_logging():
    level = logging.DEBUG if VERBOSE else logging.INFO
    logging.basicConfig(level=level, format="%(message)s")


def log_output(output, level=logging.INFO, prefix=None):
    if not output:
        return
    for line in str(output).rstrip().splitlines():
        if prefix:
            line = f"{prefix}{line}"
        LOG.log(level, "%s", line)


def err(msg, **kwargs):
    # Always report errors, including multiline subprocess diagnostics.
    log_output(msg, logging.ERROR)


def info(msg, **kwargs):
    if VERBOSE:
        LOG.debug("%s", msg)


def _decode_cfsr(cfsr: int):
    bits = [
        (0, "IACCVIOL"),
        (1, "DACCVIOL"),
        (3, "MUNSTKERR"),
        (4, "MSTKERR"),
        (5, "MLSPERR"),
        (7, "MMARVALID"),
        (8, "IBUSERR"),
        (9, "PRECISERR"),
        (10, "IMPRECISERR"),
        (11, "UNSTKERR"),
        (12, "STKERR"),
        (13, "LSPERR"),
        (15, "BFARVALID"),
        (16, "UNDEFINSTR"),
        (17, "INVSTATE"),
        (18, "INVPC"),
        (19, "NOCP"),
        (24, "UNALIGNED"),
        (25, "DIVBYZERO"),
    ]
    return [name for bit, name in bits if cfsr & (1 << bit)]


def _decode_hfsr(hfsr: int):
    bits = [(1, "VECTTBL"), (30, "FORCED"), (31, "DEBUGEVT")]
    return [name for bit, name in bits if hfsr & (1 << bit)]


def _fault_info_from_gdb(gdb_text: str) -> str:
    values = {}
    for name, value in re.findall(r"^(CFSR|HFSR|DFSR|MMFAR|BFAR|AFSR|SHCSR|CCR|MSP|PSP|LR|PC)=0x([0-9a-fA-F]+)$", gdb_text, re.MULTILINE):
        values[name] = int(value, 16)

    if not values:
        return ""

    lines = ["Fault registers:"]
    for name in ("CFSR", "HFSR", "DFSR", "MMFAR", "BFAR", "AFSR", "SHCSR", "CCR", "MSP", "PSP", "LR", "PC"):
        if name in values:
            lines.append(f"  {name}=0x{values[name]:08x}")

    cfsr_bits = _decode_cfsr(values.get("CFSR", 0))
    hfsr_bits = _decode_hfsr(values.get("HFSR", 0))
    if cfsr_bits:
        lines.append("  CFSR bits: " + ", ".join(cfsr_bits))
    if hfsr_bits:
        lines.append("  HFSR bits: " + ", ".join(hfsr_bits))

    stacked = re.search(r"^STACKED_R0_R1_R2_R3_R12_LR_PC_XPSR:\s*\n((?:0x[0-9a-fA-F]+:\s+.*\n?)?)", gdb_text, re.MULTILINE)
    if stacked:
        stack_lines = [line.strip() for line in stacked.group(1).splitlines() if line.strip()]
        if stack_lines:
            lines.append("  stacked frame dump:")
            lines.extend(f"    {line}" for line in stack_lines)

    return "\n".join(lines)


def _gdb_observed_hardfault(gdb_text: str) -> bool:
    return "[[NUCLEO-HARDFAULT]]" in gdb_text or re.search(
        r"^HardFault_Handler \(\)", gdb_text, re.MULTILINE
    ) is not None


def pack_cmdline(args, base_addr):
    """
    Pack argv for the STM32 baremetal target:
      u32 argc
      u32 argv_ptrs[argc]   (absolute addresses: base_addr + string offsets)
      NUL-terminated strings
    All fields are little-endian 32-bit.
    """
    argc = len(args)
    header_sz = 4 + 4 * argc
    ptrs = []
    strings = b""
    cur = 0
    for s in args:
        b = s.encode("utf-8") + b"\x00"
        ptrs.append(base_addr + header_sz + cur)
        strings += b
        cur += len(b)
    blob = st.pack("<I", argc) + b"".join(st.pack("<I", p) for p in ptrs) + strings
    if len(blob) > ARGV_BLOCK_SIZE:
        raise ValueError(f"argv blob is {len(blob)} bytes, exceeds {ARGV_BLOCK_SIZE}-byte block")
    return blob + bytes(ARGV_BLOCK_SIZE - len(blob))


def run(cmd, **kwargs):
    return subprocess.run(cmd, **kwargs)


def popen(cmd, **kwargs):
    return subprocess.Popen(cmd, **kwargs)


def _pick_free_port() -> int:
    s = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
    try:
        s.bind(("127.0.0.1", 0))
        return s.getsockname()[1]
    finally:
        s.close()


def _wait_for_port(host: str, port: int, timeout_s: float) -> bool:
    deadline = time.time() + timeout_s
    while time.time() < deadline:
        try:
            with socket.create_connection((host, port), timeout=0.3):
                return True
        except OSError:
            time.sleep(0.1)
    return False


def _stm32_programmer_cli(cp_path: str):
    # Accept either a direct CLI path or the containing CubeProgrammer directory.
    if not cp_path:
        return None
    candidates = []
    if os.path.isdir(cp_path):
        candidates += [
            os.path.join(cp_path, "STM32_Programmer_CLI"),
            os.path.join(cp_path, "bin", "STM32_Programmer_CLI"),
        ]
    else:
        candidates.append(cp_path)
    for candidate in candidates:
        if os.path.isfile(candidate) and os.access(candidate, os.X_OK):
            return candidate
    return None


def _cubeprogrammer_cli(st_cubeprog: str, st_clt_root: str):
    # Prefer explicit paths from the environment before falling back to PATH.
    candidates = [st_cubeprog]
    if st_clt_root:
        candidates.append(os.path.join(st_clt_root, "STM32CubeProgrammer"))
    cli = None
    for candidate in candidates:
        cli = _stm32_programmer_cli(candidate)
        if cli:
            break
    if cli is None:
        cli = shutil.which("STM32_Programmer_CLI")
    return cli


def _cubeprogrammer_connect_args(st_speed: str, st_serial: str, st_apid: str):
    # Keep reset/readback commands aligned with the selected probe speed and AP.
    args = ["-c", "port=SWD", f"freq={st_speed}"]
    connect_mode = os.environ.get("STLINK_CONNECT_MODE")
    if connect_mode:
        args.append(f"mode={connect_mode}")
    if st_serial:
        args.append(f"sn={st_serial}")
    if st_apid:
        args.append(f"ap={st_apid}")
    return args


def _run_cubeprogrammer(cli: str, connect_args, commands, verbose: bool = False) -> bool:
    # CubeProgrammer diagnostics are noisy, so log them only on failure or request.
    cmd = [cli] + connect_args + commands
    cp = run(cmd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
    if verbose or cp.returncode != 0:
        output = cp.stdout or ""
        if output:
            log_output(output, logging.DEBUG if verbose else logging.ERROR)
    return cp.returncode == 0


def _reset_target(st_cubeprog: str, st_clt_root: str, st_speed: str, st_serial: str, st_apid: str) -> bool:
    # Reset through CubeProgrammer when available; callers can still proceed if absent.
    cli = _cubeprogrammer_cli(st_cubeprog, st_clt_root)
    if cli is None:
        return False
    return _run_cubeprogrammer(cli, _cubeprogrammer_connect_args(st_speed, st_serial, st_apid), ["-rst"])


def _default_flexmem_config_elf() -> str:
    platform_dir = os.path.dirname(os.path.abspath(__file__))
    repo_root = os.path.abspath(os.path.join(platform_dir, "..", "..", "..", ".."))
    return os.path.join(repo_root, "test", "build", "nucleo-n657x0-q", "flexmem_config.elf")


def _recover_after_hardfault() -> bool:
    platform_dir = os.path.dirname(os.path.abspath(__file__))
    configure_script = os.path.join(platform_dir, "flexmem_configure.py")
    config_elf = os.environ.get("FLEXMEM_CONFIG_ELF", _default_flexmem_config_elf())

    if not os.path.exists(configure_script):
        err(f"FLEXMEM configure script not found: {configure_script}")
        return False
    if not os.path.exists(config_elf):
        err(f"FLEXMEM config ELF not found: {config_elf}")
        return False

    info("[exec_wrapper] recovering from HardFault: re-running FLEXMEM config")
    recovery_env = os.environ.copy()
    recovery_env.setdefault("STLINK_CONNECT_MODE", "UR")
    cp = run(
        [sys.executable, configure_script, config_elf],
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True,
        env=recovery_env,
    )
    if cp.returncode != 0:
        err("FLEXMEM reconfiguration after HardFault failed")
        log_output(cp.stdout, logging.ERROR)
        return False
    if VERBOSE:
        log_output(cp.stdout, logging.DEBUG)
    return True


def _run_once():
    global VERBOSE
    global STDOUT_BYTES_EMITTED
    global TARGET_FAILURE
    global TARGET_FAILURE_KIND
    global SUPPRESS_RETRYABLE_DIAGNOSTICS
    global LAST_FAULT_DIAGNOSTICS

    STDOUT_BYTES_EMITTED = 0
    TARGET_FAILURE = False
    TARGET_FAILURE_KIND = ""
    LAST_FAULT_DIAGNOSTICS = ""

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
    readelf = os.environ.get(
        "READELF",
        shutil.which("arm-none-eabi-readelf") or shutil.which("readelf") or "readelf",
    )
    port = int(os.environ.get("GDB_PORT", "3333"))
    # STM32Cube Command Line Tools integration
    # Users must install STM32CubeCLT and provide a gdbserver command.
    # Preferred: set ST_GDBSERVER_CMD as a template using Python format keys:
    #   {port} {speed} {serial} {transport} {device} {connect}
    # Example (ST-LINK_gdbserver):
    #   export ST_GDBSERVER_CMD='ST-LINK_gdbserver -p {port} -f SWD -s {speed}k'
    # Example (STM32_Programmer_CLI):
    #   export ST_GDBSERVER_CMD='STM32_Programmer_CLI -c port=SWD{serial} -s {speed} -gdbserver port={port}'
    st_gdbserver_cmd_tpl = os.environ.get("ST_GDBSERVER_CMD")
    st_speed = os.environ.get("STLINK_SPEED", "200")  # kHz (lower default for reliability)
    st_serial = os.environ.get("STLINK_SERIAL", "")    # optional, raw value
    st_transport = os.environ.get("STLINK_TRANSPORT", "SWD")
    st_device = os.environ.get("ST_DEVICE", "STM32N657X0HxQ")
    st_connect = os.environ.get("STLINK_CONNECT_MODE", "under-reset")
    st_cubeprog = os.environ.get("ST_CUBE_PROG_PATH", "")  # Path to STM32CubeProgrammer
    st_clt_root = os.environ.get("ST_CUBE_CLT_ROOT", "")  # Root of STM32CubeCLT
    st_pend = os.environ.get("STLINK_PEND_HALT_TIMEOUT", "8000")
    st_apid = os.environ.get("STLINK_APID", "")
    gdb_run_timeout = float(os.environ.get("GDB_RUN_TIMEOUT", "180"))
    # Semihosting configuration (enabled by default)
    st_semihost_port_env = os.environ.get("STLINK_SEMIHOST_PORT", "")
    try:
        st_semihost_port = int(st_semihost_port_env) if st_semihost_port_env else _pick_free_port()
    except Exception:
        st_semihost_port = _pick_free_port()
    st_semihost_level = os.environ.get("STLINK_SEMIHOST_LEVEL", "all")

    # Address extraction for argv block symbol (numeric address avoids debugger symbol issues)
    arg_block_sym = os.environ.get("ARG_BLOCK_SYMBOL", "mlkem_cmdline_block")
    arg_block_addr = None

    def _resolve_symbol_addr(elf_path: str, sym: str):
        # Try nm first: format '<addr> <type> <name>'
        try:
            cp = run([nm, "-n", elf_path], stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
            if cp.returncode == 0:
                for line in cp.stdout.splitlines():
                    parts = line.strip().split()
                    if len(parts) >= 3 and parts[-1] == sym:
                        addr_hex = parts[0]
                        if not addr_hex.startswith("0x"):
                            addr_hex = "0x" + addr_hex
                        return addr_hex
        except Exception:
            pass
        # Fallback: readelf -s
        try:
            cp = run([readelf, "-s", elf_path], stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
            if cp.returncode == 0:
                for line in cp.stdout.splitlines():
                    if sym in line:
                        fields = line.split()
                        if len(fields) >= 8 and fields[-1] == sym:
                            val = fields[1]
                            if all(c in "0123456789abcdefABCDEF" for c in val):
                                return "0x" + val
        except Exception:
            pass
        return None

    # Try both expected names in case of historical rename
    for cand in (arg_block_sym, "mlk_cmdline_block"):
        addr = _resolve_symbol_addr(elf, cand)
        if addr is not None:
            arg_block_sym = cand
            arg_block_addr = addr
            break

    # Numeric breakpoints avoid GDB symbol lookup surprises after loading RAM ELFs.
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

    # Resolve the RAM stdout buffer so GDB can dump target output after execution.
    stdout_capture_addr = _resolve_symbol_addr(elf, "nucleo_stdout_capture")
    stdout_capture_len_addr = _resolve_symbol_addr(elf, "nucleo_stdout_capture_len")
    stdout_capture_truncated_addr = _resolve_symbol_addr(elf, "nucleo_stdout_capture_truncated")
    stdout_capture_size = int(os.environ.get("NUCLEO_STDOUT_CAPTURE_SIZE", str(1536 * 1024)))
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
        err("Failed to resolve base address of argv block (mlkem_cmdline_block/mlk_cmdline_block).")
        err("- Ensure symbols are present in ELF, or set ARG_BLOCK_ADDR to the base address (hex).")
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
        # Build ST gdbserver command
        # Discover ST-LINK_gdbserver
        stlink_bin = shutil.which("ST-LINK_gdbserver")
        # Allow deriving CLT root from CubeProgrammer path if not provided
        if not st_clt_root and st_cubeprog:
            # .../STM32CubeCLT_x.y.z/STM32CubeProgrammer -> CLT root is parent dir
            st_clt_root = os.path.dirname(os.path.abspath(st_cubeprog))
            # If user pointed directly at the STM32CubeProgrammer dir, take its parent
            base = os.path.basename(st_clt_root).lower()
            if base.startswith("stm32cubeprogrammer"):
                st_clt_root = os.path.dirname(st_clt_root)
        candidate = None
        if not stlink_bin and st_clt_root:
            candidate = os.path.join(st_clt_root, "STLink-gdb-server", "bin", "ST-LINK_gdbserver")
            if os.path.isfile(candidate) and os.access(candidate, os.X_OK):
                stlink_bin = candidate

        # Auto-detect a default template if not provided
        if not st_gdbserver_cmd_tpl and stlink_bin:
            st_gdbserver_cmd_tpl = (
                f"{shlex.quote(stlink_bin)} -p {{port}} -l 1 -d -s --frequency {{speed}} {{serial_flag}} {{apid_flag}} {{cubeprog_flag}} --semihost-console-port {{semi_port}} --semihosting {{semi_level}} -g --halt --pend-halt-timeout {{pend}}"
            )

        if st_gdbserver_cmd_tpl:
            # Determine best '-cp' path for STM32CubeProgrammer CLI
            cp_path = None
            # If user provided a path
            if st_cubeprog:
                p = os.path.abspath(st_cubeprog)
                if os.path.isdir(p):
                    # If directory is 'STM32CubeProgrammer', check for CLI within
                    cli1 = os.path.join(p, "STM32_Programmer_CLI")
                    cli2 = os.path.join(p, "bin", "STM32_Programmer_CLI")
                    if os.path.isfile(cli1) and os.access(cli1, os.X_OK):
                        cp_path = p
                    elif os.path.isfile(cli2) and os.access(cli2, os.X_OK):
                        cp_path = os.path.join(p, "bin")
                elif os.path.isfile(p):
                    # User pointed directly to CLI; use its directory
                    cp_path = os.path.dirname(p)
            # If not resolved yet, try from CLT root
            if cp_path is None and st_clt_root:
                cli2 = os.path.join(os.path.abspath(st_clt_root), "STM32CubeProgrammer", "bin", "STM32_Programmer_CLI")
                if os.path.isfile(cli2) and os.access(cli2, os.X_OK):
                    cp_path = os.path.dirname(cli2)
            # If still None, try relative to ST-LINK gdbserver location
            if cp_path is None and 'stlink_bin' in locals() and stlink_bin:
                # stlink_bin .../STLink-gdb-server/bin/ST-LINK_gdbserver -> CLT root is three parents up
                root = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(stlink_bin))))
                cli2 = os.path.join(root, "STM32CubeProgrammer", "bin", "STM32_Programmer_CLI")
                if os.path.isfile(cli2) and os.access(cli2, os.X_OK):
                    cp_path = os.path.dirname(cli2)

            # Provide a flexible set of placeholders for various CLT tools.
            # - {serial}       -> raw serial value (e.g. 303030303030)
            # - {serial_flag}  -> '-i <serial>' (ST-LINK_gdbserver)
            # - {serial_prog}  -> 'sn=<serial>' (STM32_Programmer_CLI)
            # - {serial_sn}    -> ',sn=<serial>' (STM32_Programmer_CLI combined)
            # - {speed}        -> kHz value (e.g. 500)
            # - {port}         -> GDB server port (e.g. 3333)
            # - {transport}    -> SWD/JTAG (usually SWD)
            # - {device}       -> device name (e.g. STM32N657X0HxQ)
            # - {connect}      -> connection mode hint (e.g. under-reset)
            # - {cubeprog_flag}-> '-cp <path>' if resolved
            fmt = {
                "port": port,
                "speed": st_speed,
                "serial": st_serial,
                "serial_flag": (f"-i {st_serial}" if st_serial else ""),
                "serial_prog": (f"sn={st_serial}" if st_serial else ""),
                "serial_sn": (f",sn={st_serial}" if st_serial else ""),
                "transport": st_transport,
                "device": st_device,
                "connect": st_connect,
                "cubeprog": cp_path or st_cubeprog,
                "cubeprog_flag": (f"-cp {shlex.quote(cp_path)}" if cp_path else (f"-cp {shlex.quote(st_cubeprog)}" if st_cubeprog else "")),
                "pend": st_pend,
                "apid_flag": (f"-m {st_apid}" if st_apid else "-m 1"),
                "semi_port": st_semihost_port,
                "semi_level": st_semihost_level,
            }
            try:
                formatted = st_gdbserver_cmd_tpl.format(**fmt)
            except KeyError as e:
                err(f"Missing format key in ST_GDBSERVER_CMD: {e}")
                return 2
            gdbserver_cmd = shlex.split(formatted)
        else:
            msg = (
                "STM32Cube Command Line Tools required.\n"
                "- Install STM32CubeCLT (Linux/macOS).\n"
                "  Download: https://www.st.com/en/development-tools/stm32cubeclt.html\n"
                "- Set ST_GDBSERVER_CMD to a working gdbserver command template, or ensure ST-LINK_gdbserver is on PATH.\n"
                "  Examples:\n"
                "    ST-LINK_gdbserver:  'ST-LINK_gdbserver -p {port} -d --frequency {speed} {serial_flag} -g --halt {cubeprog_flag}'\n"
                "    STM32_Programmer_CLI: 'STM32_Programmer_CLI -c port={transport},{serial_prog} -s {speed} -gdbserver port={port}'\n"
                "  Tip: If ST-LINK_gdbserver errors about STM32CubeProgrammer, set ST_CUBE_PROG_PATH to its installation path,\n"
                "       or export ST_CUBE_CLT_ROOT to the CubeCLT root so the wrapper can auto-locate ST-LINK_gdbserver.\n"
            )
            # Append small diagnostics if we attempted a candidate path
            if candidate:
                msg += f"  Searched for ST-LINK_gdbserver at: {candidate}\n"
            if stlink_bin is None and shutil.which("ST-LINK_gdbserver") is None:
                msg += "  Note: ST-LINK_gdbserver not found on PATH.\n"
            err(msg)
            return 2

        info("[exec_wrapper] assuming FLEXMEM was configured by flexmem_configure.py; no runtime TCM probing")

        info(f"[exec_wrapper] starting ST gdbserver on port {port}...")
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
            # Wait for semihost console to become available and connect before attaching GDB
            # First, ensure the process is alive
            time.sleep(0.2)
            # Then, wait for the semihost port to accept connections (up to 10s)
            if not _wait_for_port("127.0.0.1", st_semihost_port, timeout_s=10.0):
                info("[exec_wrapper] semihost port not ready within timeout; continuing anyway")

            semihost_sock = None
            semihost_stop = threading.Event()
            semihost_thr = None
            semihost_exit = threading.Event()
            shared = {"exit_code": None, "stdout_streamed": False}

            def _semihost_reader(sock: socket.socket):
                global STDOUT_BYTES_EMITTED

                buf = b""
                try:
                    while not semihost_stop.is_set():
                        try:
                            data = sock.recv(4096)
                            if not data:
                                break
                            buf += data
                            while b"\n" in buf:
                                line, buf = buf.split(b"\n", 1)
                                try:
                                    text = line.decode("utf-8", errors="replace")
                                except Exception:
                                    text = line.decode(errors="replace")
                                # Detect exit sentinel first
                                t = text.strip()
                                is_exit = t.startswith("[[MLKEM-EXIT:") and t.endswith("]]")
                                if is_exit:
                                    try:
                                        code_str = t[len("[[MLKEM-EXIT:"):-2]
                                        shared["exit_code"] = int(code_str)
                                    except Exception:
                                        shared["exit_code"] = 1
                                    semihost_exit.set()
                                    # Do not log the sentinel unless verbose.
                                    if VERBOSE:
                                        LOG.debug("[semi] %s", text)
                                else:
                                    if VERBOSE:
                                        LOG.debug("[semi] %s", text)
                                    else:
                                        sys.stdout.buffer.write(line + b"\n")
                                        sys.stdout.buffer.flush()
                                        STDOUT_BYTES_EMITTED += len(line) + 1
                                        shared["stdout_streamed"] = True
                        except socket.timeout:
                            continue
                        except OSError:
                            break
                finally:
                    try:
                        sock.close()
                    except Exception:
                        pass

            # Attempt to connect the listener (non-blocking retries)
            try:
                semihost_sock = socket.create_connection(("127.0.0.1", st_semihost_port), timeout=1.0)
                semihost_sock.settimeout(0.5)
                semihost_thr = threading.Thread(target=_semihost_reader, args=(semihost_sock,), daemon=True)
                semihost_thr.start()
                info(f"[exec_wrapper] semihost listener connected on port {st_semihost_port}")
            except OSError:
                info(f"[exec_wrapper] semihost listener not connected (port {st_semihost_port}); proceeding")

            # Give the server a brief moment, then check for early exit
            time.sleep(0.8)
            if stp.poll() is not None:
                # Server exited early – surface a helpful message
                out_rem = stp.stdout.read() if stp.stdout else ""
                if out_rem and not SUPPRESS_RETRYABLE_DIAGNOSTICS:
                    log_output(out_rem, logging.DEBUG if VERBOSE else logging.ERROR)
                merged = out_rem
                low = merged.lower()
                if "firmware upgrade" in low or "upgrade required" in low:
                    # Try to suggest STLinkUpgrade locations
                    hints = []
                    if st_clt_root:
                        app1 = os.path.join(st_clt_root, "STM32CubeProgrammer", "stlink", "STLinkUpgrade")
                        app2 = os.path.join(st_clt_root, "STM32CubeProgrammer", "stlink", "STLinkUpgrade.app")
                        if os.path.exists(app1):
                            hints.append(app1)
                        if os.path.exists(app2):
                            hints.append(app2)
                    if VERBOSE:
                        err("[exec_wrapper] ST-LINK firmware upgrade required. Please run the STLinkUpgrade tool.")
                        if hints:
                            for h in hints:
                                err(f"[exec_wrapper] STLinkUpgrade candidate: {h}")
                return 2

            gdb_lines = [
                "set pagination off",
                "set confirm off",
                f"target remote localhost:{port}",
            ]
            # Write GDB commands to a temp script and run with -x
            gdb_lines += [
                # semihosting enable is handled by gdbserver; keep gdb quiet
                "load",
                f"tbreak {wrap_main_break}",
                f"jump {reset_handler_jump}",
                (f"restore {argv_bin} binary {arg_block_addr}" if arg_block_addr else f"restore {argv_bin} binary &{arg_block_sym}"),
                "break HardFault_Handler",
                "commands",
                "  echo [[NUCLEO-HARDFAULT]]\\n",
                "end",
                "break nucleo_layout_fail",
                "commands",
                "  echo [[NUCLEO-LAYOUT-FAIL]]\\n",
                "end",
                "continue",
            ]
            if stdout_capture_addr and stdout_capture_len_addr:
                # Clamp the dump length to the compile-time capture buffer size.
                gdb_lines += [
                    f"set $nucleo_stdout_len = *(unsigned int *){stdout_capture_len_addr}",
                    "if $nucleo_stdout_len > 0",
                    f"  if $nucleo_stdout_len > {stdout_capture_size}",
                    f"    set $nucleo_stdout_len = {stdout_capture_size}",
                    "  end",
                    f"  dump binary memory {stdout_capture_bin} {stdout_capture_addr} {stdout_capture_addr} + $nucleo_stdout_len",
                    "end",
                ]
            if stdout_capture_truncated_addr:
                gdb_lines += [
                    f"set $nucleo_stdout_truncated = *(unsigned int *){stdout_capture_truncated_addr}",
                    "p/x $nucleo_stdout_truncated",
                ]
            gdb_lines += [
                "info registers",
                "x/4wx $sp",
                "echo CFSR=",
                "output/x *(unsigned int *)0xE000ED28",
                "echo \\n",
                "echo HFSR=",
                "output/x *(unsigned int *)0xE000ED2C",
                "echo \\n",
                "echo DFSR=",
                "output/x *(unsigned int *)0xE000ED30",
                "echo \\n",
                "echo MMFAR=",
                "output/x *(unsigned int *)0xE000ED34",
                "echo \\n",
                "echo BFAR=",
                "output/x *(unsigned int *)0xE000ED38",
                "echo \\n",
                "echo AFSR=",
                "output/x *(unsigned int *)0xE000ED3C",
                "echo \\n",
                "echo SHCSR=",
                "output/x *(unsigned int *)0xE000ED24",
                "echo \\n",
                "echo CCR=",
                "output/x *(unsigned int *)0xE000ED14",
                "echo \\n",
                "echo MSP=",
                "output/x $msp",
                "echo \\n",
                "echo PSP=",
                "output/x $psp",
                "echo \\n",
                "echo LR=",
                "output/x $lr",
                "echo \\n",
                "echo PC=",
                "output/x $pc",
                "echo \\n",
                "echo STACKED_R0_R1_R2_R3_R12_LR_PC_XPSR:\\n",
                "if ($lr & 4)",
                "  x/8wx $psp",
                "else",
                "  x/8wx $msp",
                "end",
                "x/4wx 0xE000ED28",
                "x/wx 0xE000ED38",
            ]

            if VERBOSE:
                LOG.debug("============ GDB SCRIPT ============")
                log_output('\n'.join(gdb_lines), logging.DEBUG)
                LOG.debug("====================================")

            with tempfile.NamedTemporaryFile("w", delete=False, suffix=".gdb") as gs:
                for line in gdb_lines:
                    gs.write(line + "\n")
                gdb_script_path = gs.name

            gdb_cmd = [gdb, "--batch", "-x", gdb_script_path, elf]

            # Run GDB while streaming gdbserver output (which will include semihost output).
            info("[exec_wrapper] running gdb batch (program will continue; semihost output follows)...")
            gdbp = popen(gdb_cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
            gdb_deadline = time.time() + gdb_run_timeout if gdb_run_timeout > 0 else None

            # Stream gdbserver output until gdb finishes without blocking on readline()
            while True:
                # Early shutdown if exit sentinel observed
                if semihost_exit.is_set():
                    info("[exec_wrapper] exit sentinel detected; shutting down gdb and gdbserver...")
                    try:
                        if gdbp.poll() is None:
                            gdbp.terminate()
                            try:
                                gdbp.wait(timeout=1.0)
                            except Exception:
                                gdbp.kill()
                    except Exception:
                        pass
                    break
                if stp.stdout is not None:
                    try:
                        r, _, _ = select.select([stp.stdout], [], [], 0.1)
                        if r:
                            line = stp.stdout.readline()
                            if line:
                                # gdbserver stdout is logged only in verbose mode.
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
            layout_failed = "[[NUCLEO-LAYOUT-FAIL]]" in gdb_text
            hardfaulted = _gdb_observed_hardfault(gdb_text)
            target_failed = layout_failed or hardfaulted

            captured_text = ""
            if os.path.exists(stdout_capture_bin):
                try:
                    # Parse the same exit sentinel from dumped RAM output as from semihosting.
                    with open(stdout_capture_bin, "rb") as capture_file:
                        captured = capture_file.read()
                    captured_text = captured.decode("utf-8", errors="replace")
                    captured_lines = []
                    for capture_line in captured_text.splitlines(keepends=True):
                        stripped_line = capture_line.strip()
                        if stripped_line.startswith("[[MLKEM-EXIT:") and stripped_line.endswith("]]"):
                            try:
                                shared["exit_code"] = int(stripped_line[len("[[MLKEM-EXIT:"):-2])
                            except Exception:
                                shared["exit_code"] = 1
                            continue
                        captured_lines.append(capture_line)
                    if captured_lines and not shared.get("stdout_streamed") and not target_failed:
                        captured_output = "".join(captured_lines)
                        sys.stdout.write(captured_output)
                        sys.stdout.flush()
                        STDOUT_BYTES_EMITTED += len(captured_output.encode("utf-8"))
                except Exception as exc:
                    info(f"[exec_wrapper] failed to read stdout capture: {exc}")

            if "$nucleo_stdout_truncated = 0x1" in gdb_text:
                err("WARNING: target stdout capture truncated")

            if shared.get("exit_code") is not None:
                return int(shared["exit_code"]) if isinstance(shared["exit_code"], int) else 1

            if layout_failed:
                TARGET_FAILURE = True
                TARGET_FAILURE_KIND = "layout"
                err("FAIL!")
                err("FLEXMEM layout check failed on target")
                return 1

            if hardfaulted:
                TARGET_FAILURE = True
                TARGET_FAILURE_KIND = "hardfault"
                fault_info = _fault_info_from_gdb(gdb_text)
                LAST_FAULT_DIAGNOSTICS = fault_info
                if not SUPPRESS_RETRYABLE_DIAGNOSTICS:
                    err("FAIL!")
                    err("Target entered HardFault_Handler")
                    if fault_info:
                        err(fault_info)
                return 1

            if "Program received signal SIGTRAP" in gdb_text:
                info("[exec_wrapper] completion trap observed without exit sentinel")
                return 0

            if gdbp.returncode != 0:
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
            # Terminate ST gdbserver
            try:
                stp.terminate()
                stp.wait(timeout=1.5)
            except Exception:
                try:
                    stp.kill()
                except Exception:
                    pass
            # Stop semihost listener
            try:
                if 'semihost_stop' in locals():
                    semihost_stop.set()
                if 'semihost_sock' in locals() and semihost_sock:
                    semihost_sock.close()
                if 'semihost_thr' in locals() and semihost_thr:
                    semihost_thr.join(timeout=0.5)
            except Exception:
                pass
            # Remove the temp gdb script
            try:
                if 'gdb_script_path' in locals():
                    os.unlink(gdb_script_path)
            except Exception:
                pass


def main():
    global SUPPRESS_RETRYABLE_DIAGNOSTICS
    global LAST_FAULT_DIAGNOSTICS

    attempts = max(1, int(os.environ.get("GDB_RUN_ATTEMPTS", "2")))
    hardfault_attempts = max(0, int(os.environ.get("GDB_HARDFAULT_RECOVERY_ATTEMPTS", "1")))
    transport_retries = 0
    hardfault_recoveries = 0
    last_rc = 1

    while True:
        can_retry_transport = transport_retries < attempts - 1
        can_retry_hardfault = hardfault_recoveries < hardfault_attempts
        SUPPRESS_RETRYABLE_DIAGNOSTICS = can_retry_transport or can_retry_hardfault
        last_rc = _run_once()
        if last_rc == 0:
            return 0
        if TARGET_FAILURE_KIND == "hardfault" and can_retry_hardfault:
            hardfault_recoveries += 1
            if _recover_after_hardfault():
                if VERBOSE:
                    err(f"[exec_wrapper] retrying after recovered HardFault ({hardfault_recoveries}/{hardfault_attempts})")
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
            err(f"[exec_wrapper] retrying after transport failure ({transport_retries}/{attempts - 1})")
        time.sleep(0.5)


if __name__ == "__main__":
    raise SystemExit(main())
