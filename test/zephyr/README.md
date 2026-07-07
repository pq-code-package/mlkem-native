[//]: # (SPDX-License-Identifier: CC-BY-4.0)

# Zephyr test platform

This is a test platform that builds the mlkem-native test applications as
[Zephyr](https://www.zephyrproject.org/) applications, so they can run on
QEMU-emulated Arm MPS boards and the NUCLEO-N657X0-Q hardware board. It covers
Cortex-M3/M4/M7/M33/M55 through a single platform, without the need for
per-board hardware abstraction layers.

## Usage

The platform is selected through the `EXTRA_MAKEFILE` environment variable and
driven by the usual test targets from the top-level `Makefile`. It must run
inside the `zephyr` Nix development shell, which provides the Arm toolchain,
QEMU, and the Zephyr tree (`ZEPHYR_BASE`). The board is chosen with the
`ZEPHYR_TARGET` environment variable (default `mps3-an547`):

```
export EXTRA_MAKEFILE=test/zephyr/platform.mk
export ZEPHYR_TARGET=mps3-an547
nix develop .#zephyr --command ./scripts/tests func --opt=opt
```

Currently supported targets:

| `ZEPHYR_TARGET`     | Zephyr board             | Runner         | Core       |
| ------------------- | ------------------------ | -------------- | ---------- |
| `mps2-an385`        | `mps2/an385`             | `mps2-an385`   | Cortex-M3  |
| `mps2-an386`        | `mps2/an386`             | `mps2-an386`   | Cortex-M4  |
| `mps2-an500`        | `mps2/an500`             | `mps2-an500`   | Cortex-M7  |
| `mps2-an521`        | `mps2/an521/cpu0`        | `mps2-an521`   | Cortex-M33 |
| `mps3-an547`        | `mps3/corstone300/an547` | `mps3-an547`   | Cortex-M55 |
| `nucleo-n657x0-q`   | `nucleo_n657x0_q`        | OpenOCD + GDB  | Cortex-M55 |

The Armv8.1-M MVE FIPS202 backend is an `OPT=1` feature and is built for
`mps3-an547` and `nucleo-n657x0-q`.

## How it works

Test binaries are built as Zephyr applications using Zephyr's standard
CMake-based build, registered as a `CUSTOM_BUILD` hook in mlkem-native's
makefiles.

The Zephyr application lives in `app/`:

- `app/CMakeLists.txt` compiles the `mlkem_native.c` amalgamation, the test
  sources, and `shim.c`. The test's `main()` is renamed to `mlk_test_main` via
  `-Dmain=mlk_test_main` so the shim can own `main()`.
- `app/shim.c` fetches argv via semihosting, calls `mlk_test_main`, and exits
  QEMU with the test's return code (again via semihosting).
- `app/Kconfig` force-selects the FPU/MVE features for Corstone-300, whose
  Zephyr SoC does not otherwise advertise MVE.

`platform.mk` forwards the test binary's full `CFLAGS` to the CMake build, so
the firmware is compiled with the project's own warning/optimization/standard
policy and feature defines rather than a divergent Zephyr default.

`exec_wrapper.py` runs a built ELF under QEMU (`-nographic`, semihosting on),
forwarding the guest's exit code; it is wired in as `EXEC_WRAPPER`.
