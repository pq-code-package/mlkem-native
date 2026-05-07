<!--
Copyright (c) The mldsa-native project authors
Copyright (c) The mlkem-native project authors
Copyright (c) Arm Ltd.
SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
-->

# NUCLEO-N657X0-Q Baremetal Platform

This platform runs ML-KEM tests on the ST NUCLEO-N657X0-Q board with STM32Cube Command Line Tools plus ST-LINK GDB server, or with OpenOCD when `NUCLEO_DEBUG_BACKEND=openocd` is selected. The board is never flashed: the FLEXMEM config binary is downloaded into RAM, and test binaries are loaded into RAM with GDB `load`.

## Required Workflow

STM32N657X0 starts with 64 KiB ITCM and 128 KiB DTCM. Tests require 256 KiB ITCM and 256 KiB DTCM, so CI uses a deterministic two-binary sequence. Both binaries are loaded into RAM; nothing is written to flash.

1. Connect to the board with STM32CubeProgrammer over SWD and reset it. For board recovery, run this FLEXMEM stage with `STLINK_CONNECT_MODE=UR` so CubeProgrammer uses connect-under-reset.
2. Load `flexmem_config.elf` into the default reset-time RAM layout, run it, poll `SYSCFG->CM55TCMCR` until it reports the expanded FLEXMEM layout, then reset the target again.
3. Start `ST-LINK_gdbserver` against the reset target and connect `arm-none-eabi-gdb` with `target remote localhost:<port>`. The default runtime server command does not request connect-under-reset.
4. GDB `load`s the test ELF into the expanded ITCM/DTCM layout and starts it from `Reset_Handler`.
5. C startup clears `.bss`; GDB stops at `__wrap_main` and restores the packed command-line blob into the ITCM-resident `mlk_cmdline_block`.
6. The wrapper continues execution, captures stdout, and uses `[[MLKEM-EXIT:<rc>]]` as the exit sentinel.

RAM is wiped by reset; the test ELF and argv blob are loaded only after the config binary has completed and the target has been reset into the expanded layout.

## Connection

The host tools connect to the NUCLEO-N657X0-Q through the on-board ST-LINK using SWD. The default backend uses `STM32_Programmer_CLI` for `flexmem_configure.py`; `exec_wrapper.py` starts `ST-LINK_gdbserver` and then runs `arm-none-eabi-gdb` in batch mode. Set `NUCLEO_DEBUG_BACKEND=openocd` to use OpenOCD for both the FLEXMEM config stage and the runtime GDB server.

The default connection is intentionally conservative for reliability:

- CubeProgrammer calls use `-c port=SWD freq=${STLINK_SPEED:-200}` and add `mode=${STLINK_CONNECT_MODE}` only when `STLINK_CONNECT_MODE` is set. Use `STLINK_CONNECT_MODE=UR` for the FLEXMEM config stage when the board must be recovered under reset.
- OpenOCD calls use `interface/stlink.cfg`, `target/stm32n6x.cfg`, `transport select swd`, and `adapter speed ${OPENOCD_SPEED:-${STLINK_SPEED:-200}}`; `OPENOCD`, `OPENOCD_INTERFACE`, and `OPENOCD_TARGET` can override these defaults.
- `STLINK_SERIAL=<serial>` selects one probe when multiple ST-LINKs are attached.
- `STLINK_APID=<ap>` is forwarded to CubeProgrammer as `ap=<ap>` and to `ST-LINK_gdbserver` as `-m <ap>`.
- Runtime GDB sessions use `GDB_PORT=${GDB_PORT:-3333}`; set `STLINK_SEMIHOST_PORT` to pin the semihost console port, otherwise the wrapper picks a free localhost port.
- The default runtime `ST-LINK_gdbserver` command does not consume `STLINK_CONNECT_MODE`, so test ELFs are not loaded with connect-under-reset in the standard flow. If you provide a custom `ST_GDBSERVER_CMD` that uses `{connect}`, do not let it request under-reset for the test binary: resetting under GDB can discard the FLEXMEM layout that was just latched.

`exec_wrapper.py` auto-locates `ST-LINK_gdbserver` from `PATH` or `ST_CUBE_CLT_ROOT`. If needed, `ST_GDBSERVER_CMD` can override the server command template. The template accepts placeholders such as `{port}`, `{speed}`, `{serial_flag}`, `{apid_flag}`, `{cubeprog_flag}`, `{semi_port}`, `{semi_level}`, and `{pend}`.

## FLEXMEM Expansion and Reboot

`flexmem_configure.py` performs the memory expansion before any RAM-resident test is loaded:

1. Resolve `main` and `_estack` in `flexmem_config.elf` with `arm-none-eabi-nm`.
2. Reset the target with CubeProgrammer. If `STLINK_CONNECT_MODE=UR` is set, the subsequent RAM download/start sequence connects under reset.
3. Download the config ELF into the default reset-time RAM layout with `STM32_Programmer_CLI -c port=SWD freq=<kHz> [mode=UR] -halt -d <elf>`, or with OpenOCD `load_image` when `NUCLEO_DEBUG_BACKEND=openocd` is selected.
4. Seed `MSP=<_estack>` and `PC=<main|1>` with `-coreReg`, then `-run` the config binary directly from RAM.
5. The config binary writes `SYSCFG->CM55TCMCR` so both ITCM and DTCM are configured as 256 KiB, then stops at a breakpoint.
6. The host polls `SYSCFG->CM55TCMCR` at `0x56008008` in HOTPLUG mode until `(value & 0xff) == 0x99`.
7. The host resets the target again so the new FLEXMEM layout is applied before the test ELF is loaded.

The reset after configuration is required: FLEXMEM register writes are latched for the next boot, and the reset also clears the RAM contents used by the config helper.

## GDB Runtime Load

After FLEXMEM expansion and reset, `run_test_after_flexmem.py` delegates to `exec_wrapper.py`. In the standard ST-LINK flow, the default `ST-LINK_gdbserver` command does not use connect-under-reset for this runtime connection. In the OpenOCD flow, the runtime server uses `reset_config srst_only srst_nogate` and does not request `connect_assert_srst`. Avoid custom runtime templates that request under-reset: the reset performed by an under-reset GDB-server connection can lose the expanded FLEXMEM configuration before `load` writes the test ELF. The wrapper creates a temporary GDB script and runs:

```
arm-none-eabi-gdb --batch -x <generated-script.gdb> <test-elf>
```

The generated GDB script follows this order:

1. `target remote localhost:<GDB_PORT>` connects to `ST-LINK_gdbserver`.
2. `load` writes the test ELF sections into expanded ITCM, DTCM, and AXI SRAM according to `linker/ram_secure.ld`.
3. `tbreak <__wrap_main>` installs a temporary breakpoint after C runtime startup, using a numeric address when symbol resolution succeeds.
4. `jump *<Reset_Handler|1>` starts the image as a Thumb Cortex-M program.
5. `restore <argv.bin> binary <mlk_cmdline_block address>` writes the packed argv blob after startup has cleared `.bss`.
6. Breakpoints are installed for `HardFault_Handler` and `nucleo_layout_fail`, then `continue` runs the test.
7. At completion, GDB dumps the RAM stdout capture buffer and fault diagnostics if needed.

The wrapper terminates `ST-LINK_gdbserver` after each run. If `load` fails before target output, or if the target enters `HardFault_Handler`, the wrapper can re-run `flexmem_configure.py` and retry according to the recovery environment variables documented below.

## Prerequisites

- STM32Cube CLT with `ST-LINK_gdbserver`, `STM32_Programmer_CLI`, and `arm-none-eabi-gdb`.
- For `NUCLEO_DEBUG_BACKEND=openocd`, the `.#st-openocd` Nix package provides an OpenOCD build with native ST-LINK support and `target/stm32n6x.cfg`. Stock OpenOCD 0.12.0 is not sufficient for this backend.
- A NUCLEO-N657X0-Q connected over USB.
- Run all commands from the board devshell:

```
nix develop .#nucleo-n657x0-q
```

Useful environment variables:

```
export ST_CUBE_CLT_ROOT=/opt/ST/STM32CubeCLT_1.20.0
export ST_CUBE_PROG_PATH=/opt/ST/STM32CubeCLT_1.20.0/STM32CubeProgrammer/bin
export STLINK_SERIAL=<your-stlink-serial>
export STLINK_SPEED=200
export GDB_PORT=3333
```

To use OpenOCD instead of STM32Cube CLT / `ST-LINK_gdbserver`:

```
export NUCLEO_DEBUG_BACKEND=openocd
export OPENOCD_SPEED=200
```

The `nucleo-n657x0-q` devshell includes `.#st-openocd` on `PATH`, so `OPENOCD` only needs to be set when using a non-Nix OpenOCD build.

When running the stages manually, scope connect-under-reset to the FLEXMEM configuration command only:

```
STLINK_CONNECT_MODE=UR \
  python3 test/baremetal/platform/nucleo-n657x0-q/flexmem_configure.py \
    test/build/nucleo-n657x0-q/flexmem_config.elf

unset STLINK_CONNECT_MODE
python3 test/baremetal/platform/nucleo-n657x0-q/run_test_after_flexmem.py \
  test/build/mlkem512/bin/test_mlkem512
```

The wrappers also accept `ST_GDBSERVER_CMD`, `STLINK_APID`, `STLINK_SEMIHOST_PORT`, `STLINK_SEMIHOST_LEVEL`, `STLINK_PEND_HALT_TIMEOUT`, `GDB`, `NM`, and `READELF`.

The OpenOCD backend also accepts `OPENOCD_INTERFACE` and `OPENOCD_TARGET` if the installed OpenOCD uses non-standard script locations or a patched STM32N6 target script.

## Build

Build the FLEXMEM config binary and one RAM-only test binary:

```
make flexmem_config func_512 EXTRA_MAKEFILE=test/baremetal/platform/nucleo-n657x0-q/platform.mk -j1 V=1
```

The config binary is:

```
test/build/nucleo-n657x0-q/flexmem_config.elf
```

An example test binary is:

```
test/build/mlkem512/bin/test_mlkem512
```

## Run in CI

Run the full deterministic sequence for `test_mlkem512`. The Make targets do not set `STLINK_CONNECT_MODE`; they inherit it from the environment if present:

```
make run_flexmem_test EXTRA_MAKEFILE=test/baremetal/platform/nucleo-n657x0-q/platform.mk -j1 V=1
```

Or run each stage explicitly:

```
STLINK_CONNECT_MODE=UR \
  python3 test/baremetal/platform/nucleo-n657x0-q/flexmem_configure.py \
    test/build/nucleo-n657x0-q/flexmem_config.elf

unset STLINK_CONNECT_MODE
python3 test/baremetal/platform/nucleo-n657x0-q/run_test_after_flexmem.py \
  test/build/mlkem512/bin/test_mlkem512
```

`run_test_after_flexmem.py` delegates to `exec_wrapper.py`, which starts ST-LINK GDB server, loads the ELF into RAM, runs from `Reset_Handler`, restores argv into `mlk_cmdline_block` at `__wrap_main`, dumps the target stdout capture buffer, and returns the `[[MLKEM-EXIT:<rc>]]` code.

The KAT and ACVP run targets depend on `run_flexmem_config`, so `make run_kat` and `make run_acvp` restore the expanded FLEXMEM layout before loading the RAM-resident images. `exec_wrapper.py` retries once after pre-output GDB transport failures; set `GDB_RUN_ATTEMPTS=<n>` to adjust this. If the initial GDB `load` command reports `load failed` before target output starts, the wrapper re-runs `flexmem_configure.py` and retries the same ELF once; set `GDB_LOAD_FAILURE_RECOVERY_ATTEMPTS=<n>` to adjust or disable this. If the target enters `HardFault_Handler`, the wrapper re-runs the FLEXMEM config binary and retries once; set `GDB_HARDFAULT_RECOVERY_ATTEMPTS=<n>` to adjust this.

Recovery runs launched by `exec_wrapper.py` default `STLINK_CONNECT_MODE` to `UR` for the reconfiguration step, without changing the default runtime GDB-server command used for the retried test ELF.

Manual hardware validation for load-failure recovery can force the retry path by resetting the board to its default FLEXMEM layout, building `flexmem_config` and a test ELF, then running `python3 test/baremetal/platform/nucleo-n657x0-q/run_test_after_flexmem.py test/build/mlkem512/bin/test_mlkem512` without a prior `run_flexmem_config` step.

## Argv Blob Loading

Target arguments are passed through a RAM blob rather than through semihosting or debugger command-line support. The test image links `cmdline_region.c`, which reserves the 64 KiB `mlk_cmdline_block` symbol in ITCM. `exec_wrapper.py` resolves that symbol with `arm-none-eabi-nm`, falling back to `readelf -s`; `ARG_BLOCK_SYMBOL` can select a different symbol and `ARG_BLOCK_ADDR` can override the resolved address.

The wrapper packs its target argv into a temporary binary file with this little-endian layout:

- `uint32_t argc`
- `uint32_t argv[argc]`, where each entry is an absolute target address inside the same blob
- NUL-terminated UTF-8 argument strings immediately after the pointer table

The GDB command sequence intentionally loads the argv blob after C startup reaches `__wrap_main`: first `load` writes the ELF sections into RAM, then `jump Reset_Handler|1` runs normal startup and zeroes `.bss`, then a temporary breakpoint stops at `__wrap_main`, and only then GDB executes `restore <argv.bin> binary <mlk_cmdline_block address>`. Loading the blob at this point prevents startup `.bss` initialization from erasing it. `__wrap_main` casts `mlk_cmdline_block` to the command-line structure and calls the real ML-KEM test `main(argc, argv)`.

## Memory Layout

`linker/flexmem_config_default.ld` is used only by the config binary:

- vector/code: SRAM available in the default reset layout
- data/stack: default 128 KiB DTCM
- no flash memory regions or flash LMAs

`linker/ram_secure.ld` is used by tests after FLEXMEM reset has applied:

- vector table and executable sections: expanded 256 KiB ITCM at `0x00000000`
- `.data`, `.bss`: expanded 256 KiB DTCM at `0x30000000`
- argv block: expanded 256 KiB ITCM at `0x00000000`
- stdout capture: AXI SRAM at `0x34080000`
- stack: top 192 KiB of DTCM, with `_estack = 0x30040000` and `__StackLimit = 0x30010000`
- no flash memory regions or flash LMAs

## Layout Validation

Each test binary links `flexmem_layout_check.c` and calls it before ML-KEM tests. It fails with a breakpoint if either expanded region is unavailable:

- executes `nucleo_itcm_above_default_probe()` from `.itcm_probe` placed beyond the default 64 KiB ITCM boundary
- writes and reads address `0x30020000`, beyond the default 128 KiB DTCM boundary

This proves the CI flow loaded the test after FLEXMEM configuration and reset. Actual pass/fail execution remains hardware-dependent on the connected board, ST-LINK firmware, and CLT version.

## Notes

- Do not use debugger GUI flows; CI uses ST-LINK GDB server plus `arm-none-eabi-gdb` only.
- Do not run the test binary directly on a freshly reset board; it links into expanded ITCM/DTCM that does not exist until after `flexmem_config.elf` and reset.
- Do not reintroduce runtime probing or linker wrapping of `SystemInit`; FLEXMEM configuration is deterministic and reset-applied.
- Keep target output on normal libc/newlib `printf` and file-I/O paths linked with `--specs=rdimon.specs -lc -lrdimon`; the platform `_write` captures stdout/stderr in RAM for GDB to harvest because raw semihosting `bkpt 0xab` syscalls are not reliable on this board.
