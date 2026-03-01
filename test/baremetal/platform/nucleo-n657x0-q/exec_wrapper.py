#!/usr/bin/env python3
# Copyright (c) The mldsa-native project authors
# Copyright (c) The mlkem-native project authors
# Copyright (c) Arm Ltd.
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

import os
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


def err(msg, **kwargs):
    # Always print errors
    print(msg, file=sys.stderr, **kwargs)


def info(msg, **kwargs):
    if VERBOSE:
        print(msg, file=sys.stderr, **kwargs)


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
    return st.pack("<I", argc) + b"".join(st.pack("<I", p) for p in ptrs) + strings


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


def main():
    global VERBOSE

    argv = sys.argv[1:]
    # Minimal flag parsing for wrapper flags (remove them from argv)
    if "--verbose" in argv:
        VERBOSE = True
        argv.remove("--verbose")
    if "-v" in argv:
        VERBOSE = True
        argv.remove("-v")

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

    blob = pack_cmdline(args, base_addr)

    with tempfile.TemporaryDirectory() as td:
        argv_bin = os.path.join(td, "argv.bin")
        with open(argv_bin, "wb") as f:
            f.write(blob)

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
                f"{shlex.quote(stlink_bin)} -p {{port}} -l 1 -d -s --frequency {{speed}} {{serial_flag}} {{apid_flag}} {{cubeprog_flag}} -g --semihost-console-port {{semi_port}} --semihosting {{semi_level}} --initialize-reset --halt --pend-halt-timeout {{pend}}"
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
                # stlink_bin .../STLink-gdb-server/bin/ST-LINK_gdbserver -> root is two parents up
                root = os.path.dirname(os.path.dirname(os.path.abspath(stlink_bin)))
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
                "    ST-LINK_gdbserver:  'ST-LINK_gdbserver -p {port} -d --frequency {speed} {serial_flag} --initialize-reset {cubeprog_flag}'\n"
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
            shared = {"exit_code": None}

            def _semihost_reader(sock: socket.socket):
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
                                    # Do not print the sentinel unless verbose
                                    if VERBOSE:
                                        print(f"[semi] {text}")
                                else:
                                    # Print semihost line; prefix only in verbose mode
                                    if VERBOSE:
                                        print(f"[semi] {text}")
                                    else:
                                        print(text)
                        except socket.timeout:
                            continue
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
                if out_rem and VERBOSE:
                    print(out_rem, end="")
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

            # Write GDB commands to a temp script and run with -x
            gdb_lines = [
                "set pagination off",
                "set confirm off",
                f"target remote localhost:{port}",
                "monitor reset",
                # semihosting enable is handled by gdbserver; keep gdb quiet
                "load",
                "tbreak __wrap_main",
                "continue",
                (f"restore {argv_bin} binary {arg_block_addr}" if arg_block_addr else f"restore {argv_bin} binary &{arg_block_sym}"),
                "continue",
            ]

            with tempfile.NamedTemporaryFile("w", delete=False, suffix=".gdb") as gs:
                for line in gdb_lines:
                    gs.write(line + "\n")
                gdb_script_path = gs.name

            gdb_cmd = [gdb, "--batch", "-x", gdb_script_path, elf]

            # Run GDB while streaming gdbserver output (which will include semihost output).
            info("[exec_wrapper] running gdb batch (program will continue; semihost output follows)...")
            gdbp = popen(gdb_cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)

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
                                # gdbserver stdout (printed only in verbose mode)
                                if VERBOSE:
                                    print(line, end="")
                    except Exception:
                        # If select/readline fails, avoid blocking the loop
                        pass
                # Check if gdb has completed
                if gdbp.poll() is not None:
                    break

            out, errout = gdbp.communicate()
            if out and VERBOSE:
                print(out, end="")
            if errout and VERBOSE:
                # gdb chatter / errors (verbose only)
                err(errout, end="")

            if shared.get("exit_code") is not None:
                return int(shared["exit_code"]) if isinstance(shared["exit_code"], int) else 1

            if gdbp.returncode != 0:
                err("FAIL!")
                err(f"gdb batch failed with code {gdbp.returncode}")
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


if __name__ == "__main__":
    raise SystemExit(main())
