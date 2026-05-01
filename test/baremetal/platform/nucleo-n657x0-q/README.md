<!--
Copyright (c) The mldsa-native project authors
Copyright (c) The mlkem-native project authors
Copyright (c) Arm Ltd.
SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
-->

# NUCLEO-N657X0-Q Baremetal Platform

This platform runs ML-KEM tests on the ST NUCLEO-N657X0-Q board with STM32Cube Command Line Tools and ST-LINK GDB server. The board is never flashed: both the FLEXMEM config binary and test binaries are loaded into RAM with GDB `load`.

## Required Flow

STM32N657X0 starts with 64 KiB ITCM and 128 KiB DTCM. Tests require 256 KiB ITCM and 256 KiB DTCM, so CI uses a deterministic two-binary sequence:

1. Load `flexmem_config.elf` into default-reset RAM.
2. Run it until `SYSCFG->CM55TCMCR` reports the expected FLEXMEM layout, then print `FLEXMEM configuration complete; reset target and load test binary.` on the host.
3. Stop the GDB server session.
4. Reset/reconnect the target.
5. Load the test ELF into the expanded ITCM/DTCM RAM layout.
6. Run the test, dump the target stdout capture buffer at the final breakpoint, and use `[[MLKEM-EXIT:<rc>]]` as the exit sentinel.

RAM is wiped by reset; the test ELF is loaded only after the config binary has completed and the target has been reset.

## Prerequisites

- STM32Cube CLT with `ST-LINK_gdbserver`, `STM32_Programmer_CLI`, and `arm-none-eabi-gdb`.
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

The wrappers also accept `ST_GDBSERVER_CMD`, `STLINK_APID`, `STLINK_SEMIHOST_PORT`, `STLINK_SEMIHOST_LEVEL`, `STLINK_PEND_HALT_TIMEOUT`, `GDB`, `NM`, and `READELF`.

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

Run the full deterministic sequence for `test_mlkem512`:

```
make run_flexmem_test EXTRA_MAKEFILE=test/baremetal/platform/nucleo-n657x0-q/platform.mk -j1 V=1
```

Or run each stage explicitly:

```
python3 test/baremetal/platform/nucleo-n657x0-q/flexmem_configure.py \
  test/build/nucleo-n657x0-q/flexmem_config.elf

python3 test/baremetal/platform/nucleo-n657x0-q/run_test_after_flexmem.py \
  test/build/mlkem512/bin/test_mlkem512
```

`run_test_after_flexmem.py` delegates to `exec_wrapper.py`, which starts ST-LINK GDB server, loads the ELF into RAM, injects argv into `mlk_cmdline_block`, runs from `Reset_Handler`, dumps the target stdout capture buffer, and returns the `[[MLKEM-EXIT:<rc>]]` code.

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
