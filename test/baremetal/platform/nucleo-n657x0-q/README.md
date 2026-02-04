<!--
Copyright (c) The mldsa-native project authors
Copyright (c) Arm Ltd.
SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
-->

# NUCLEO-N657X0-Q Baremetal Platform

This platform runs ML-KEM tests on the ST NUCLEO‑N657X0‑Q board using STM32Cube Command Line Tools (CLT) and ST‑LINK gdbserver. The `exec_wrapper.py` launches the gdbserver, injects argv into target memory, streams semihost output, and runs a batch `gdb` session against the board.

## Prerequisites
- Install STM32Cube CLT (includes ST‑LINK gdbserver and STM32CubeProgrammer):
  - Download: https://www.st.com/en/development-tools/stm32cubeclt.html
  - Verify tools are present on your PATH (example macOS install path):
    - `/opt/ST/STM32CubeCLT_<ver>/STLink-gdb-server/bin/ST-LINK_gdbserver`
    - `/opt/ST/STM32CubeCLT_<ver>/STM32CubeProgrammer/bin/STM32_Programmer_CLI`
- Hardware: NUCLEO‑N657X0‑Q connected over USB. Update ST‑LINK firmware if prompted:
  - macOS app: `<CLT>/STM32CubeProgrammer/stlink/STLinkUpgrade.app`
  - CLI: `<CLT>/STM32CubeProgrammer/stlink/STLinkUpgrade`

## Environment Variables (exec_wrapper.py)
- `GDB` (default: `arm-none-eabi-gdb`) – gdb binary.
- `GDB_PORT` (default: `3333`) – gdbserver port.
- `ST_CUBE_CLT_ROOT` – CLT root; helps auto‑locate gdbserver and CLI.
- `ST_CUBE_PROG_PATH` – path to `STM32_Programmer_CLI` bin dir; passed via `-cp`.
- `ST_GDBSERVER_CMD` – optional template to override gdbserver command.
- `STLINK_SPEED` (default: `200`) – SWD speed in kHz (e.g. `50` for reliability).
- `STLINK_SERIAL` – ST‑LINK serial string (strongly recommended when multiple probes).
- `STLINK_APID` (default: `1`) – Access Port/core selection.
- `STLINK_TRANSPORT` (default: `SWD`) – debug transport.
- `STLINK_CONNECT_MODE` (default: `under-reset`) – connection mode hint.
- `ST_DEVICE` (default: `STM32N657X0HxQ`) – device name hint (not always used).
- `STLINK_PEND_HALT_TIMEOUT` (default: `8000`) – pending halt timeout (ms).
- `STLINK_SEMIHOST_PORT` (default: auto) – semihost console TCP port.
- `STLINK_SEMIHOST_LEVEL` (default: `all`) – semihosting level (gdbserver).

## Recommended ST‑LINK gdbserver template
- Default baseline (auto‑selected when available; expanded by the wrapper):
```
ST-LINK_gdbserver -p {port} -l 1 -d -s --frequency {speed} {serial_flag} {apid_flag} {cubeprog_flag}   -g --semihost-console-port {semi_port} --semihosting {semi_level}   --initialize-reset --halt --pend-halt-timeout {pend}
```
- Placeholders:
  - `{serial_flag}` → `-i <serial>` if `STLINK_SERIAL` set; else empty
  - `{apid_flag}` → `-m <apid>` if `STLINK_APID` set; else `-m 1`
  - `{cubeprog_flag}` → `-cp <path>` if `ST_CUBE_PROG_PATH` or auto‑located
  - `{port}`, `{speed}`, `{semi_port}`, `{semi_level}`, `{pend}` – from env/defaults

Alternative (STM32_Programmer_CLI gdbserver):
```
STM32_Programmer_CLI -c port={transport} freq={speed} {serial_prog} -gdbserver port={port}
```
- `{serial_prog}` → `sn=<serial>` if `STLINK_SERIAL` set

## Semihost output and verbosity
- The wrapper enables semihosting in the gdbserver and connects a TCP listener before GDB attaches.
- Each semihost line is prefixed with `[semi] `; only semihost lines print by default.
- Add `--verbose` (or `-v`) to print wrapper diagnostics, gdbserver output, and gdb chatter.

## Argv injection
- Tests receive arguments via a memory block named `mlkem_cmdline_block`.
- The wrapper packs argv into a temporary `argv.bin` and restores it via GDB:
  - Resolves the symbol’s numeric address using `arm-none-eabi-nm` (fallback: `readelf -s`).
  - Uses `restore <argv.bin> binary <addr>` in the GDB batch.
- Manual generator: `test/baremetal/platform/nucleo-n657x0-q/make_argv_bin.py`
  - Example: `python3 .../make_argv_bin.py /tmp/argv.bin <arg0> [arg1 ...]`

## Quick start
1) Set environment (adjust paths/serial):
```
export ST_CUBE_CLT_ROOT=/opt/ST/STM32CubeCLT_1.20.0
export ST_CUBE_PROG_PATH=/opt/ST/STM32CubeCLT_1.20.0/STM32CubeProgrammer/bin
export STLINK_SERIAL=<your-serial>
export STLINK_SPEED=50
export GDB_PORT=61234
```
2) Run a single test binary directly:
```
python3 test/baremetal/platform/nucleo-n657x0-q/exec_wrapper.py --verbose   test/build/mlkem512/bin/test_mlkem512
```
3) Or via Makefile targets (from repo root):
```
make run_func_512 EXTRA_MAKEFILE=test/baremetal/platform/nucleo-n657x0-q/platform.mk -j1 V=1
```

## Manual GDB session (advanced)
```
# In a terminal, start gdbserver manually (example):
ST-LINK_gdbserver -p 61234 -l 1 -d -s -cp "$ST_CUBE_PROG_PATH" -m 1   --semihost-console-port 7185 --semihosting all --initialize-reset --halt --pend-halt-timeout 8000

# In another terminal (gdb):
(gdb) file <ELF>
(gdb) target remote :61234
(gdb) monitor reset
(gdb) load
(gdb) restore /tmp/argv.bin binary &mlkem_cmdline_block     # or numeric address
(gdb) monitor reset
(gdb) continue
```

## Troubleshooting
- USB/Probe: If you see `DEV_USB_COMM_ERR` or timeouts, unplug/replug, try a different USB port, and update ST‑LINK firmware.
- Probe selection: set `STLINK_SERIAL=<serial>` to disambiguate.
- Speed: reduce `STLINK_SPEED` (e.g., `50`) for stability.
- Tools not found: set `ST_CUBE_CLT_ROOT` and/or `ST_CUBE_PROG_PATH` so the wrapper can find `ST-LINK_gdbserver` and `STM32_Programmer_CLI`.
- Semihost port: if the listener can’t connect in time, the wrapper proceeds; try a fixed `STLINK_SEMIHOST_PORT`.

## Notes
- ST‑LINK gdbserver does not implement the QEMU semihost `SYS_EXIT_EXTENDED`. A sentinel‑based exit workaround is planned in the proposal.
- This platform uses FSBL‑LRUN startup/system/linker from the Cube template and a 128 KiB stack for tests.
