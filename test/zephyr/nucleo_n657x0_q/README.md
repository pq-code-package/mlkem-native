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
- GDB argv insertion after Zephyr startup reaches `__wrap_main`.

Test output uses ITM stimulus port 0 and OpenOCD SWO capture. The host wrapper
decodes that SWO stream and keeps OpenOCD/GDB control chatter out of stdout
unless `--verbose` is passed.

## Files

- `exec_wrapper.py`: configures FLEXMEM, starts OpenOCD with SWO capture
  enabled, loads a Zephyr ELF with GDB, restores the packed argv blob, decodes
  ITM port 0 output, and reads the target return code at `nucleo_test_done`.
- `nucleo_host/`: Python helpers for FLEXMEM configuration, argv packing,
  OpenOCD command generation, GDB script generation, symbol lookup, fault
  diagnostics.

The Zephyr application shim lives in `test/zephyr/app/shim_nucleo_n657x0_q.c`.

## Run

Use the Zephyr platform makefile and select the NUCLEO target:

```sh
nix develop .#zephyr
make run_func_512 EXTRA_MAKEFILE=test/zephyr/platform.mk ZEPHYR_TARGET=nucleo-n657x0-q
```

The execution wrapper configures FLEXMEM before each ELF run. The supported
Zephyr hardware run targets are:

```text
run_kat run_func run_acvp run_wycheproof
```

The top-level `make test` target also includes generic unit, alloc, and RNG
failure tests; those are not wired as NUCLEO Zephyr applications.

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

STM32N657X0 starts with a smaller reset-time TCM layout. The NUCLEO runner
expands both ITCM and DTCM before each RAM-loaded Zephyr test:

1. OpenOCD attaches with `reset_config none`.
2. The script enables the SYSCFG clock by setting bit 0 in `RCC_APB4ENSR2` at
   `0x56028a78`.
3. It read-modify-writes `SYSCFG_CM55TCMCR` at `0x56008008` so the low byte is
   `0x99`.
4. It sets bit 0 in `SYSCFG_CM55RSTCR` at `0x56008018`.
5. It polls until `(SYSCFG_CM55TCMCR & 0xff) == 0x99`.
6. It runs `reset run` so the expanded layout is applied before the Zephyr ELF
   is loaded.
