[//]: # (SPDX-License-Identifier: CC-BY-4.0)

# Building mlkem-native

### Prerequisites

To build **mlkem-native**, you need `make` and a C90 compiler. To use the test scripts, you need Python3 (>= 3.7).

### By hand

See [mlkem](mlkem).

### Using `make`

You can build and test **mlkem-native** as follows:

```bash
make test       # With native code backend (if available)
make OPT=0 test # With C backend
```

To merely build test components, use the following `make` targets:

```bash
make func
make kat
make acvp
```

To run them, add `run_`:

```bash
make run_func
make run_kat
make run_acvp
```

The resulting binaries can be found in `test/build` (their full path is printed by `make`).

For benchmarking, specify the cycle counting method. Currently, **mlkem-native** is supporting NO, PERF, PMU, and MAC:
* `NO` means that no cycle counting will be used; this can be used to confirm that benchmarks compile fine.
* `PERF` uses the `perf` kernel module for cycle counting. Does not work on Apple platforms.
* `PMU` uses direct PMU access if available. On AArch64, this may require you to load a kernel module first, see [here](https://github.com/mupq/pqax?tab=readme-ov-file#enable-access-to-performance-counters). Does not work on Apple platforms.
* `MAC` is `perf`-based and works on some Apple platforms, at least Apple M1.

```
# CYCLES has to be one of PERF, PMU, MAC, NO
sudo make run_bench CYCLES=PERF
sudo make run_bench_components CYCLES=PERF
```

### Using `tests` script

For convenience, you can also use the [`./scripts/tests`](scripts/tests) script as a wrapper around `make`. For
example,

```bash
./scripts/tests func
```

will compile and run functionality tests. Similarly,

```bash
./scripts/tests bench -c PERF -r
```

will compile and run benchmarks, using PERF for cycle counting (`-c PERF`) and running as root (`-r`).

#### Cross-compilation

To cross-compile and run the tests for another architecture under QEMU, use the `--cross {ARCH}`
flag. It sets sensible defaults for `--cross-prefix`, `--cflags`, `--ldflags` and `--exec-wrapper`
that work out of the box in the corresponding `nix` shell (`nix develop .#cross-{ARCH}`), which
provides the matching cross toolchain and QEMU and which you have to enter yourself:

```bash
# On any host, cross-compile and run AArch64 tests under QEMU:
nix develop .#cross-aarch64 --command ./scripts/tests func --cross aarch64 -v
```

Each target pairs with the `nix develop .#cross-{ARCH}` shell of the same name and sets the
following defaults:

| `--cross`    | `--cross-prefix`                | `--cflags`                       | `--ldflags` | `--exec-wrapper`                       |
|--------------|---------------------------------|----------------------------------|-------------|----------------------------------------|
| `x86_64`     | `x86_64-unknown-linux-gnu-`     | `-DMLK_FORCE_X86_64`             |             | `qemu-x86_64`                          |
| `aarch64`    | `aarch64-unknown-linux-gnu-`    | `-DMLK_FORCE_AARCH64`            |             | `qemu-aarch64`                         |
| `aarch64_be` | `aarch64_be-none-linux-gnu-`    | `-static -DMLK_FORCE_AARCH64_EB` | `-static`   | `qemu-aarch64_be`                      |
| `ppc64le`    | `powerpc64le-unknown-linux-gnu-`| `-DMLK_FORCE_PPC64LE -mcpu=power8`|            | `qemu-ppc64le -cpu power8`             |
| `riscv64`    | `riscv64-unknown-linux-gnu-`    | `-DMLK_FORCE_RISCV64`            |             | `qemu-riscv64 -cpu rv64,v=true,vlen=128`|
| `riscv32`    | `riscv32-unknown-linux-gnu-`    | `-DMLK_FORCE_RISCV32`            |             | `qemu-riscv32`                         |

A few notes:

* Explicit flags override the preset. For example, to use a different RISC-V vector length, pass
  `-w "qemu-riscv64 -cpu rv64,v=true,vlen=256"`; to build PPC64LE for POWER7 instead of POWER8, pass
  `--cflags="-mcpu=power7"`.
* Architecture ISA feature flags (`-mavx2`, `-march=armv8.4-a+sha3`, `-march=rv64gcv`) are added
  automatically by the Makefile in the default `--auto` mode, so keep `--auto` on for optimized
  builds.

For detailed information on how to use the script, please refer to
`./scripts/tests --help`.

### Windows

You can also build **mlkem-native** on Windows using `nmake` and an MSVC compiler.

To build and run the tests (only support functional testing for non-opt implementation for now), use the following `nmake` targets:
```powershell
nmke /f .\Makefile.Microsoft_nmake quickcheck
```

# Checking the proofs

## CBMC

### Prerequisites

To run the CBMC proofs, you need specific versions of CBMC and the underlying solvers, e.g. as specified in our `nix` environment; see [nix/cbmc](nix/cbmc/).
See [CONTRIBUTING.md](CONTRIBUTING.md) for instructions on how to setup and use `nix`.

### Running the CBMC proofs

Once you are in the `nix` shell or have all tools setup by hand, use `./scripts/tests cbmc` (or just `tests cbmc` in the `nix` shell) to re-check the CBMC proofs.
See `tests cbmc --help` for details on the command line options, and [proofs/cbmc](proofs/cbmc) for more details on the CBMC proofs in general.

## HOL-Light

### Prerequisites

To run the HOL-Light proofs, you need recent versions of HOL-Light and s2n-bignum, e.g. as specified in our `nix` environment; see [nix/s2n_bignum](nix/s2n_bignum) and [nix/hol_light](nix/hol_light).
See [CONTRIBUTING.md](CONTRIBUTING.md) for instructions on how to setup and use `nix`.

### Running the HOL-Light proofs

Once you are in the `nix` shell or have all tools setup by hand, use `./scripts/tests hol_light` (or just `tests hol_light` in the `nix` shell) to re-check the HOL-Light proofs. Note that depending on the function, they will take a long time. See `tests hol_light --help` for details on the command line options, and [proofs/hol_light](proofs/hol_light) for more details on the HOL-Light proofs in general.
