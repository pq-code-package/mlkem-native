<!--
Copyright (c) The mldsa-native project authors
Copyright (c) The mlkem-native project authors
Copyright (c) Arm Ltd.
SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
-->

# NUCLEO-N657X0-Q Zephyr Hardware Helpers

This directory contains the NUCLEO-N657X0-Q Zephyr hardware entry point and
supporting host/debug helpers. The board is not flashed: OpenOCD first expands
FLEXMEM with direct register writes, then GDB loads the Zephyr ELF into RAM.

Only two target-specific behaviors remain here:

- FLEXMEM expansion for the STM32N657X0 ITCM/DTCM layout.
- GDB bootargs insertion after Zephyr startup reaches `get_bootargs()`.

Test output uses ITM stimulus port 0 and OpenOCD SWO capture. The host wrapper
decodes that SWO stream and keeps OpenOCD/GDB control chatter out of stdout
unless `--verbose` is passed.

## Files

- `exec_wrapper.py`: configures FLEXMEM, starts OpenOCD with SWO capture
  enabled, loads a Zephyr ELF with GDB, restores the dynamic bootargs string,
  decodes ITM port 0 output, and reads the target return code at
  `nucleo_test_done`.
- `nucleo_host/`: Python helpers for FLEXMEM configuration, OpenOCD command
  generation, GDB script generation, symbol lookup, fault diagnostics.

The Zephyr application shim lives in `test/zephyr/app/shim_nucleo_n657x0_q.c`.

## Run

Use the Zephyr platform makefile and select the NUCLEO target:

```sh
nix develop .#zephyr
make run_func_512 EXTRA_MAKEFILE=test/zephyr/platform.mk ZEPHYR_TARGET=nucleo-n657x0-q
```

The execution wrapper configures FLEXMEM before each ELF run. The working
Zephyr hardware run targets are:

```text
run_kat run_func run_unit run_alloc run_rng_fail run_acvp run_wycheproof
```

Known exceptions:

- `run_stack` is a host-side stack analysis target. In this platform mode it
  builds a Zephyr Arm ELF, then the stack script attempts to execute that ELF
  on the host.
- `run_abicheck` is not currently built as a NUCLEO Zephyr application when
  `OPT=1`; the NUCLEO wrapper expects the Zephyr shim symbols used for bootargs
  injection and completion reporting.

Benchmark targets remain explicit and require the usual `CYCLES` setting:

```sh
make run_bench_512 CYCLES=NO EXTRA_MAKEFILE=test/zephyr/platform.mk ZEPHYR_TARGET=nucleo-n657x0-q
make run_bench_components_512 CYCLES=NO EXTRA_MAKEFILE=test/zephyr/platform.mk ZEPHYR_TARGET=nucleo-n657x0-q
```

Useful environment variables:

```sh
export OPENOCD_SPEED=8000
export OPENOCD_SERIAL=<optional-probe-serial>
export GDB_PORT=3333
export SWO_TRACECLK=100000000
export SWO_PIN_FREQ=1000000
```

`OPENOCD`, `OPENOCD_INTERFACE`, `OPENOCD_TARGET`, `OPENOCD_TRANSPORT`, `GDB`,
`NM`, and `READELF` can override the default tools and OpenOCD scripts.

## FLEXMEM Sequence

Zephyr's default NUCLEO-N657X0-Q RAM region is a 2 MiB SRAM window starting at
`0x34000000`; its first 400 KiB is the STM32N657X0 FLEXRAM allocation. After
reset, the Cortex-M55 TCM layout is 64 KiB ITCM and 128 KiB DTCM. The NUCLEO
runner repurposes FLEXMEM to expand the TCMs to 256 KiB ITCM and 256 KiB DTCM
before each RAM-loaded Zephyr test, so the test image is linked above that low
AXISRAM/FLEXRAM window instead of using the board default:

1. OpenOCD attaches with `reset_config none`.
2. The script enables the SYSCFG clock by setting bit 0 in `RCC_APB4ENSR2` at
   `0x56028a78`.
3. It read-modify-writes `SYSCFG_CM55TCMCR` at `0x56008008` so the low byte is
   `0x99`.
4. It sets bit 0 in `SYSCFG_CM55RSTCR` at `0x56008018`.
5. It polls until `(SYSCFG_CM55TCMCR & 0xff) == 0x99`.
6. It runs `reset run` so the expanded layout is applied before the Zephyr ELF
   is loaded.

The board is RAM-loaded, not flashed. Zephyr's default NUCLEO-N657X0-Q RAM
region is a 2 MiB SRAM window starting at `0x34000000`; its first 400 KiB is
the STM32N657X0 FLEXRAM allocation. The hardware benchmark setup is the reason
this target uses a board-specific memory layout: before each run, the hardware
wrapper repurposes FLEXMEM to expand the Cortex-M55 TCMs by setting the low
byte of `SYSCFG_CM55TCMCR` to `0x99`, selecting 256 KiB ITCM and 256 KiB DTCM,
then resets the target so that layout is active. Because this changes the low
AXISRAM/FLEXRAM window that the default Zephyr layout would use, the test image
is instead linked in a 192 KiB AXISRAM window at `0x34080000`; see
`nucleo_n657x0_q/README.md` for the exact register sequence.

Test stdout is captured over ITM stimulus port 0 through SWO. This avoids using
semihosting for normal output: semihosting is blocking and each host operation
requires debug exception/interrupt handling, which makes it too slow and too
intrusive for repeated hardware test and benchmark runs. SWO is also simpler
than UART in this setup because the OpenOCD SWO endpoint is tied directly to
the selected debug probe, while UART output requires identifying the correct
virtual COM port for that specific probe.
