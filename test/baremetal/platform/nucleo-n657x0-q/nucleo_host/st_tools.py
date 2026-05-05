# Copyright (c) The mlkem-native project authors
# Copyright (c) Arm Ltd.
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

"""Locate STM32CubeCLT tools and build common ST-LINK command arguments."""

import os
import shutil
import subprocess


def find_cubeprogrammer_cli(cp_path="", st_clt_root=""):
    """Find ``STM32_Programmer_CLI`` from explicit paths, CLT root, or PATH."""
    candidates = []
    if cp_path:
        if os.path.isdir(cp_path):
            candidates.extend([
                os.path.join(cp_path, "STM32_Programmer_CLI"),
                os.path.join(cp_path, "bin", "STM32_Programmer_CLI"),
            ])
        else:
            candidates.append(cp_path)
    if st_clt_root:
        candidates.append(os.path.join(st_clt_root, "STM32CubeProgrammer", "bin", "STM32_Programmer_CLI"))
    path_candidate = shutil.which("STM32_Programmer_CLI")
    if path_candidate:
        candidates.append(path_candidate)
    for candidate in candidates:
        if candidate and os.path.isfile(candidate) and os.access(candidate, os.X_OK):
            return candidate
    return None


def connect_args(speed="200", serial="", apid="", mode=None):
    """Return CubeProgrammer ``-c`` arguments for one SWD connection."""
    args = ["-c", "port=SWD", f"freq={speed}"]
    if mode:
        args.append(f"mode={mode}")
    if serial:
        args.append(f"sn={serial}")
    if apid:
        args.append(f"ap={apid}")
    return args


def run_quiet(cmd):
    """Run a command with stdout and stderr merged for delayed diagnostics."""
    return subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)


def derive_clt_root(st_cubeprog: str):
    """Infer the STM32CubeCLT root from a CubeProgrammer path if possible."""
    if not st_cubeprog:
        return ""
    st_clt_root = os.path.dirname(os.path.abspath(st_cubeprog))
    if os.path.basename(st_clt_root).lower().startswith("stm32cubeprogrammer"):
        st_clt_root = os.path.dirname(st_clt_root)
    return st_clt_root


def find_stlink_gdbserver(st_clt_root=""):
    """Find ``ST-LINK_gdbserver`` on PATH or below the provided CLT root."""
    stlink_bin = shutil.which("ST-LINK_gdbserver")
    candidate = None
    if not stlink_bin and st_clt_root:
        candidate = os.path.join(st_clt_root, "STLink-gdb-server", "bin", "ST-LINK_gdbserver")
        if os.path.isfile(candidate) and os.access(candidate, os.X_OK):
            stlink_bin = candidate
    return stlink_bin, candidate


def cubeprogrammer_cp_path(st_cubeprog="", st_clt_root="", stlink_bin=""):
    """Return the directory to pass as ST-LINK GDB server's ``-cp`` value."""
    cp_path = None
    if st_cubeprog:
        path = os.path.abspath(st_cubeprog)
        if os.path.isdir(path):
            cli1 = os.path.join(path, "STM32_Programmer_CLI")
            cli2 = os.path.join(path, "bin", "STM32_Programmer_CLI")
            if os.path.isfile(cli1) and os.access(cli1, os.X_OK):
                cp_path = path
            elif os.path.isfile(cli2) and os.access(cli2, os.X_OK):
                cp_path = os.path.join(path, "bin")
        elif os.path.isfile(path):
            cp_path = os.path.dirname(path)

    if cp_path is None and st_clt_root:
        cli2 = os.path.join(os.path.abspath(st_clt_root), "STM32CubeProgrammer", "bin", "STM32_Programmer_CLI")
        if os.path.isfile(cli2) and os.access(cli2, os.X_OK):
            cp_path = os.path.dirname(cli2)

    if cp_path is None and stlink_bin:
        root = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(stlink_bin))))
        cli2 = os.path.join(root, "STM32CubeProgrammer", "bin", "STM32_Programmer_CLI")
        if os.path.isfile(cli2) and os.access(cli2, os.X_OK):
            cp_path = os.path.dirname(cli2)

    return cp_path
