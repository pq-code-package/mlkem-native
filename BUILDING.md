[//]: # (SPDX-License-Identifier: CC-BY-4.0)

# Building mlkem-native

### Prerequisites

To build **mlkem-native**, you need `make` and a C90 compiler. To use the test scripts, you need Python3 (>= 3.7).

### Using `make`

You can build and test **mlkem-native** as follows:

```bash
make test       # With native code backend (if available)
make OPT=0 test # With C backend
```

To merely build test components, use the following `make` targets:

```bash
make func
make nistkat
make kat
make acvp
```

To run them, add `run_`:

```bash
make run_func
make run_nistkat
make run_kat
make run_acvp
```

The resulting binaries can be found in `test/build` (their full path is printed by `make`).

For benchmarking, specify the cycle counting method. Currently, **mlkem-native** is supporting PERF, PMU (AArch64 and
x86 only), M1 (Apple Silicon only):

```
# CYCLES has to be on of PERF, PMU, M1, NO
make run_bench CYCLES=PERF
make run_bench_components CYCLES=PERF
```

### Using `tests` script

For convenience, you can also use the [`./scripts/tests`](scripts/tests) script as a wrapper around `make`. For
example,

```bash
./scripts/tests func
```

will compile and run functionality tests. For detailed information on how to use the script, please refer to
`./scripts/tests --help`.

### Windows

You can also build **mlkem-native** on Windows using `nmake` and an MSVC compiler.

To build and run the tests (only support functional testing for non-opt implementation for now), use the following `nmake` targets:
```powershell
nmke /f .\Makefile.Microsoft_nmake quickcheck
```

# Checking the proofs

### Prerequisites

To run the CBMC proofs, you need the CBMC version as specified in our `nix` development environment. Please setup `nix`
as described in [CONTRIBUTING.md](CONTRIBUTING.md).

### Running CBMC

To check the CBMC proofs, enter the `nix` development environment and use `tests cbmc`.
