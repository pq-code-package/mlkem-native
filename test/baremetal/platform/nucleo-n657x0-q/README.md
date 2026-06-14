<!--
Copyright (c) The mldsa-native project authors
Copyright (c) The mlkem-native project authors
Copyright (c) Arm Ltd.
SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
-->

# NUCLEO-N657X0-Q Baremetal Platform

This platform runs ML-KEM tests on the ST NUCLEO-N657X0-Q board using the
Nix-provided OpenOCD backend. The board is never flashed: the FLEXMEM config
binary is downloaded into RAM, and test binaries are loaded into RAM with GDB
`load`.

## Required Workflow

STM32N657X0 starts with 64 KiB ITCM and 128 KiB DTCM. Tests require 256 KiB
ITCM and 256 KiB DTCM, so CI uses a deterministic two-binary sequence. Both
binaries are loaded into RAM; nothing is written to flash.

1. Start OpenOCD for the FLEXMEM stage with connect-under-reset enabled.
2. Load `flexmem_config.elf` into the default reset-time RAM layout, set
   `MSP=<_estack>` and `PC=<main|1>`, run it, poll `SYSCFG->CM55TCMCR` at
   `0x56008008` until `(value & 0xff) == 0x99`, then `reset run` so the
   expanded layout is latched.
3. Start a fresh OpenOCD runtime GDB server without connect-under-reset.
4. GDB `load`s the test ELF into the expanded ITCM/DTCM layout and starts it
   from `Reset_Handler`.
5. C startup clears `.bss`; GDB stops at `__wrap_main` and restores the packed
   command-line blob into the ITCM-resident `mlk_cmdline_block`.
6. The wrapper continues execution, dumps the RAM stdout capture buffer, and
   uses `[[MLKEM-EXIT:<rc>]]` as the exit sentinel.

The FLEXMEM config stage uses connect-under-reset. The runtime test stage does
not request connect-under-reset.

## Connection

The host tools connect to the NUCLEO-N657X0-Q through the on-board debug probe
using SWD. OpenOCD uses `interface/stlink.cfg`, `target/stm32n6x.cfg`,
`transport select swd`, and `adapter speed ${OPENOCD_SPEED:-8000}` by default.

Useful environment variables:

```
export OPENOCD_SPEED=8000
export OPENOCD_SERIAL=<optional-probe-serial>
export GDB_PORT=3333
```

`OPENOCD`, `OPENOCD_INTERFACE`, `OPENOCD_TARGET`, and `OPENOCD_TRANSPORT` can
override the executable, script names, and transport when needed. `GDB`, `NM`,
and `READELF` can override the binary utilities.

The 8 MHz SWD default matches the ST tools' successful recovery connection for
this board. Very low SWD speeds can leave OpenOCD waiting on the SWD DP in
some post-test states.

## FLEXMEM Expansion and Reboot

`flexmem_configure.py` performs the memory expansion before any RAM-resident
test is loaded:

1. Resolve `main` and `_estack` in `flexmem_config.elf` with
   `arm-none-eabi-nm`.
2. Generate an OpenOCD script that uses
   `reset_config srst_only srst_nogate connect_assert_srst`, then `reset halt`.
3. Download the config ELF into the default reset-time RAM layout with
   `load_image`.
4. Seed `MSP=<_estack>` and `PC=<main|1>`, then `resume` the config binary
   directly from RAM.
5. Poll `SYSCFG->CM55TCMCR` at `0x56008008` until `(value & 0xff) == 0x99`.
6. Switch OpenOCD reset handling back to a Cortex-M system reset with
   `reset_config none`, then run `reset run` so the new FLEXMEM layout is
   applied before the test ELF is loaded.

The reset after configuration is required: FLEXMEM register writes are latched
for the next boot, and the reset also clears the RAM contents used by the config
helper.

## GDB Runtime Load

After FLEXMEM expansion and reset, `run_test_after_flexmem.py` delegates to
`exec_wrapper.py`. The runtime OpenOCD server uses
`reset_config srst_only srst_nogate` and halts without requesting another
reset. The wrapper
creates a temporary GDB script and runs:

```
arm-none-eabi-gdb --batch -x <generated-script.gdb> <test-elf>
```

The generated GDB script follows this order:

1. `target remote localhost:<GDB_PORT>` connects to OpenOCD.
2. `load` writes the test ELF sections into expanded ITCM, DTCM, and AXI SRAM
   according to `linker/ram_secure.ld`.
3. `tbreak <__wrap_main>` installs a temporary breakpoint after C runtime
   startup, using a numeric address when symbol resolution succeeds.
4. `jump *<Reset_Handler|1>` starts the image as a Thumb Cortex-M program.
5. `restore <argv.bin> binary <mlk_cmdline_block address>` writes the packed
   argv blob after startup has cleared `.bss`.
6. Breakpoints are installed for `HardFault_Handler` and `nucleo_layout_fail`,
   then `continue` runs the test.
7. At completion, GDB dumps the RAM stdout capture buffer and fault diagnostics
   if needed.
8. GDB asks OpenOCD to switch to `reset_config none` and `reset run` after
   harvesting output so the next FLEXMEM setup starts from a fresh boot state.

The wrapper terminates OpenOCD after each run. If `load` fails before target
output, or if the target enters `HardFault_Handler`, the wrapper can re-run
`flexmem_configure.py` and retry according to the recovery environment variables
documented below.

## Prerequisites

- A NUCLEO-N657X0-Q connected over USB.
- The board devshell, which provides `arm-none-eabi-gdb` and the
  `.#openocd-unstable` package:

```
nix develop .#nucleo-n657x0-q
```

The `.#openocd-unstable` package (nixpkgs' OpenOCD git snapshot) provides native
debug probe support and `target/stm32n6x.cfg`. Stock OpenOCD 0.12.0 is not
sufficient for this board flow.

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

## Run

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

The KAT and ACVP run targets depend on `run_flexmem_config`, so `make run_kat`
and `make run_acvp` restore the expanded FLEXMEM layout before loading the
RAM-resident images.

`exec_wrapper.py` retries once after pre-output GDB transport failures; set
`GDB_RUN_ATTEMPTS=<n>` to adjust this. If the initial GDB `load` command
reports `load failed` before target output starts, the wrapper re-runs
`flexmem_configure.py` and retries the same ELF once; set
`GDB_LOAD_FAILURE_RECOVERY_ATTEMPTS=<n>` to adjust or disable this. If the target
enters `HardFault_Handler`, the wrapper re-runs the FLEXMEM config binary and
retries once; set `GDB_HARDFAULT_RECOVERY_ATTEMPTS=<n>` to adjust this.

Manual hardware validation for load-failure recovery can force the retry path by
resetting the board to its default FLEXMEM layout, building `flexmem_config` and
a test ELF, then running the test wrapper without a prior `run_flexmem_config`
step:

```
python3 test/baremetal/platform/nucleo-n657x0-q/run_test_after_flexmem.py \
  test/build/mlkem512/bin/test_mlkem512
```

## Argv Blob Loading

Target arguments are passed through a RAM blob rather than through debugger
command-line support. The test image links `cmdline_region.c`, which reserves
the 64 KiB `mlk_cmdline_block` symbol in ITCM. `exec_wrapper.py` resolves that
symbol with `arm-none-eabi-nm`, falling back to `readelf -s`;
`ARG_BLOCK_SYMBOL` can select a different symbol and `ARG_BLOCK_ADDR` can
override the resolved address.

The wrapper packs its target argv into a temporary binary file with this
little-endian layout:

- `uint32_t argc`
- `uint32_t argv[argc]`, where each entry is an absolute target address inside
  the same blob
- NUL-terminated UTF-8 argument strings immediately after the pointer table

The GDB command sequence intentionally loads the argv blob after C startup
reaches `__wrap_main`: first `load` writes the ELF sections into RAM, then
`jump Reset_Handler|1` runs normal startup and zeroes `.bss`, then a temporary
breakpoint stops at `__wrap_main`, and only then GDB executes
`restore <argv.bin> binary <mlk_cmdline_block address>`. Loading the blob at
this point prevents startup `.bss` initialization from erasing it.
`__wrap_main` casts `mlk_cmdline_block` to the command-line structure and calls
the real ML-KEM test `main(argc, argv)`.

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
- stack: top 192 KiB of DTCM, with `_estack = 0x30040000` and
  `__StackLimit = 0x30010000`
- no flash memory regions or flash LMAs

## Layout Validation

Each test binary links `flexmem_layout_check.c` and calls it before ML-KEM
tests. It fails with a breakpoint if either expanded region is unavailable:

- executes `nucleo_itcm_above_default_probe()` from `.itcm_probe` placed beyond
  the default 64 KiB ITCM boundary
- writes and reads address `0x30020000`, beyond the default 128 KiB DTCM
  boundary

This proves the CI flow loaded the test after FLEXMEM configuration and reset.
Actual pass/fail execution remains hardware-dependent on the connected board,
probe firmware, and OpenOCD behavior.

## Notes

- Do not use debugger GUI flows; CI uses OpenOCD plus `arm-none-eabi-gdb` only.
- Do not run the test binary directly on a freshly reset board; it links into
  expanded ITCM/DTCM that does not exist until after `flexmem_config.elf` and
  reset.
- Do not reintroduce runtime probing or linker wrapping of `SystemInit`;
  FLEXMEM configuration is deterministic and reset-applied.
- Keep target output on normal libc/newlib `printf` and file-I/O paths linked
  with `--specs=rdimon.specs -lc -lrdimon`; the platform `_write` captures
  stdout/stderr in RAM for GDB to harvest because raw semihosting `bkpt 0xab`
  syscalls are not reliable on this board.
