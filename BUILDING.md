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

For benchmarking, specify the measurement method. Currently, **mlkem-native** is supporting NO, PERF, PMU, MAC_KPC, and MAC_NS:
* `NO` means that no cycle counting will be used; this can be used to confirm that benchmarks compile fine.
* `PERF` uses the `perf` kernel module for cycle counting. Does not work on Apple platforms.
* `PMU` uses direct PMU access if available. On AArch64, this may require you to load a kernel module first, see [here](https://github.com/mupq/pqax?tab=readme-ov-file#enable-access-to-performance-counters). Does not work on Apple platforms.
* `MAC_KPC` counts cycles through Apple's private `kperf` framework and works on some Apple platforms, at least Apple M1. It has to run as root, and recent macOS versions deny the required configuration even to root on recent Apple silicon.
* `MAC_NS` uses `clock_gettime_nsec_np()` and works on all Apple platforms without special privileges. It reports **elapsed nanoseconds instead of cycles**, so results are meaningful for relative comparisons on one machine but are not cycle counts.

Benchmarking binaries print the unit of their measurements alongside each result, i.e. `cycles` for the cycle-counting methods and `ns` for `MAC_NS`.

```
# CYCLES has to be one of PERF, PMU, MAC_KPC, MAC_NS, NO
sudo make run_bench CYCLES=PERF
sudo make run_bench_components CYCLES=PERF

# MAC_NS needs no elevated privileges
make run_bench CYCLES=MAC_NS
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

For detailed information on how to use the script, please refer to
`./scripts/tests --help`.

### Windows

You can also build **mlkem-native** on Windows using `nmake` and an MSVC compiler.

To build and run the tests, use the following `nmake` target:
```powershell
nmake /f .\Makefile.Microsoft_nmake quickcheck
```

This runs the functional, RNG-failure, allocation, ACVP, KAT and Wycheproof tests. The assembly backends are not yet
supported on Windows, so the tests are built for the C backend only.

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
