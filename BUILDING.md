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

#### Test platforms

The `--platform` option supplies non-empty cross-compilation and execution
settings, or selects the platform Makefile. It does not change which tests run.
Empty low-level options and profile values that are not specified preserve the
existing environment. The `native` profile adds no compile or run overrides.

```bash
# Native host
./scripts/tests func

# GNU/Linux AArch64 under QEMU user mode
nix develop .#cross-aarch64 --command \
  ./scripts/tests func --platform linux/aarch64

# No-MMU AArch64 QEMU virt machine
nix develop .#cross-aarch64-embedded --command \
  ./scripts/tests func --platform baremetal/aarch64-virt

# AVR under simavr
nix develop .#cross-avr --command \
  ./scripts/tests func --platform baremetal/avr --opt=no_opt

# Zephyr on the default QEMU board
nix develop .#zephyr --command \
  ./scripts/tests func --platform zephyr
```

Available profiles:

| Platform | Nix shell | Execution environment |
| -------- | --------- | --------------------- |
| `native` | `default` | Inherited environment (normally the current host) |
| `linux/x86_64` | `cross-x86_64` or `cross` | QEMU user mode |
| `linux/x86_64-no-avx2` | `cross-x86_64` or `cross` | QEMU Snowridge, no AVX2 |
| `linux/aarch64` | `cross-aarch64` or `cross` | QEMU user mode |
| `linux/aarch64_be` | `cross-aarch64_be` or `cross` | QEMU user mode |
| `linux/ppc64le-power8` | `cross-ppc64le` or `cross` | QEMU POWER8 |
| `linux/ppc64le-power7` | `cross-ppc64le` or `cross` | POWER7 code on QEMU POWER8 |
| `linux/riscv64-rvv128` | `cross-riscv64` or `cross` | QEMU RVV, VLEN=128 |
| `linux/riscv64-rvv256` | `cross-riscv64` or `cross` | QEMU RVV, VLEN=256 |
| `linux/riscv64-rvv512` | `cross-riscv64` or `cross` | QEMU RVV, VLEN=512 |
| `linux/riscv64-rvv1024` | `cross-riscv64` or `cross` | QEMU RVV, VLEN=1024 |
| `linux/riscv32` | `cross-riscv32` or `cross` | QEMU user mode |
| `baremetal/aarch64-virt` | `cross-aarch64-embedded` | QEMU system emulation |
| `baremetal/avr` | `cross-avr` | simavr |
| `zephyr` | `zephyr` | Zephyr under QEMU or on supported hardware |

Explicit non-empty `--cross-prefix` and `--exec-wrapper` values override
profile values; empty values are treated like omitted options. `--cflags` and
`--ldflags` extend profile values. Bare-metal and Zephyr profiles select
their existing platform Makefile, which supplies toolchain, linker, and runtime
defaults.

The standalone example Makefiles do not consume platform Makefiles. The
`examples` command, and `all` unless passed `--no-examples`, therefore reject
bare-metal, Zephyr, and explicit `--extra-makefile` configurations. Prefix-based
Linux profiles remain supported.

For detailed information on how to use the script, please refer to
`./scripts/tests --help`.

### Windows

You can also build **mlkem-native** on Windows using `nmake` and an MSVC compiler.

To build and run the tests, use the following `nmake` target:
```powershell
nmake /f .\Makefile.Microsoft_nmake quickcheck
```

This runs the functional, RNG-failure, allocation, ACVP, KAT and Wycheproof tests.

Full assembly support is provided for both x86-64 and ARM64 (AArch64). The following NMake options are available:

| Option    | Description                                                  |
| --------- | ------------------------------------------------------------ |
| ASSEMBLY= | Build with assembly enabled (x86-64); requires ml64.exe (Microsoft Macro Assembler) |
| ARM64=    | (requires ASSEMBLY=) Build with assembly enabled (ARM64/AArch64); requires armasm64.exe (Microsoft ARM64 assembler) |
| OPT_MOST= | (*independent of assembly*) Use the maximum optimization switches /Ox /Ob2 /Oi /Ot /Oy instead of only /O2 |
| DEBUG=    | (*independent of assembly*) Compile with /Od and generate debug information with /Zi |

#### Examples (Windows x86-64)

Build with x86-64 assembly (Microsoft x64 ABI):

```powershell
nmake /f Makefile.Microsoft_nmake ASSEMBLY= clean quickcheck
```

Build with assembly and maximum optimization:

```powershell
nmake /f Makefile.Microsoft_nmake ASSEMBLY= OPT_MOST= clean quickcheck
```

Build with x86-64 assembly, unoptimized C code, and debugging information enabled:

```powershell
nmake /f Makefile.Microsoft_nmake ASSEMBLY= DEBUG= clean quickcheck
```

#### Examples (Windows ARM64)

Build with ARM64 assembly:

```powershell
nmake /f Makefile.Microsoft_nmake ASSEMBLY= ARM64= clean quickcheck
```

Build with ARM64 assembly and maximum optimization:

```powershell
nmake /f Makefile.Microsoft_nmake ASSEMBLY= ARM64= OPT_MOST= clean quickcheck
```

All tests have been executed on Windows 11/64bit (ALL PASSED); on an AMD Ryzen 9 8945HS and on a Snapdragon(R) X (X126100, Qualcomm(R) Oryon(TM) CPU).

#### Notes on MS Windows assembly ports

- For x86-64, the code was ported manually from the System V AMD64 ABI to the Microsoft x64 ABI.
- GitHub Copilot and Anthropic's Claude subsequently optimized register usage in some of the .asm sources.
- For ARM64, the Linux and Windows ABIs are compatible. The sources were reformatted for armasm64.exe, and assembler pseudo-instructions were added.
- Alternatively, the ARM64 assembly files can be compiled with clang-cl (it must be selected explicitly in the Visual Studio Installer).
- For ARM64, SEH unwind codes (PDATA and XDATA sections) were added by hand.
- armasm64.exe has two severe bugs, which are worked around as follows:
  - ALIGN directives pad with zeros instead of proper NOPs (HINT #0x0), and the zeros cause CPU exceptions when executed. Workaround: the ALIGN directives are replaced with explicit NOP instructions.
  - armasm64.exe does not honor the `RELOC 2` suffix, which is required in the PDATA section. Workaround: a small Python script (written by Anthropic's Claude) patches the .obj files right after they are assembled.

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
