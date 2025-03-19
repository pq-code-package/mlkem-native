[//]: # (SPDX-License-Identifier: CC-BY-4.0)

# HOL Light functional correctness proofs

This directory contains functional correctness proofs for fast AArch64 assembly routines
used in mlkem-native. The proofs were largely developed by John Harrison
and are written in the [HOL Light](https://hol-light.github.io/) theorem
prover, utilizing the assembly verification infrastructure from [s2n-bignum](https://github.com/awslabs/s2n-bignum).

Each function is proved in a separate `.ml` file in [proofs/](proofs). Each file
contains the byte code being verified, as well as the specification that is being
proved. Specifications are essentially Hoare triples, with the noteworthy difference
that the program is implicit as the content of memory at the PC; which is asserted to
be the code under verification as part of the precondition.

## What is covered?

At present, this directory contains functional correctness proofs for the following functions:

- ML-KEM Arithmetic:
  * AArch64 forward NTT: [mlkem_ntt.S](mlkem/mlkem_ntt.S)
  * AArch64 inverse NTT: [mlkem_intt.S](mlkem/mlkem_intt.S)
  * AArch64 conversion to Montgomery form: [mlkem_poly_tomont.S](mlkem/mlkem_poly_tomont.S)
  * AArch64 modular reduction: [mlkem_poly_reduce.S](mlkem/mlkem_poly_reduce.S)
  * AArch64 'multiplication cache' computation: [mlkem_poly_mulcache_compute.S](mlkem/mlkem_poly_mulcache_compute.S)
- FIPS202:
  * Keccak-F1600 using lazy rotations (see [this paper](https://eprint.iacr.org/2022/1243)): [keccak_f1600_x1_scalar.S](mlkem/keccak_f1600_x1_scalar.S)
  * Keccak-F1600 using v8.4-A SHA3 instructions: [keccak_f1600_x1_v84a.S](mlkem/keccak_f1600_x1_v84a.S)
  * 2-fold Keccak-F1600 using v8.4-A SHA3 instructions: [keccak_f1600_x2_v84a.S](mlkem/keccak_f1600_x2_v84a.S)
  * 'Hybrid' 4-fold Keccak-F1600 using scalar and v8-A Neon instructions: [keccak_f1600_x4_v8a_scalar.S](mlkem/keccak_f1600_x4_v8a_scalar.S)
  * 'Triple hybrid' 4-fold Keccak-F1600 using scalar, v8-A Neon and v8.4-A+SHA3 Neon instructions:[keccak_f1600_x4_v8a_v84a_scalar.S](mlkem/keccak_f1600_x4_v8a_v84a_scalar.S)

The NTT and invNTT functions are super-optimized using [SLOTHY](https://github.com/slothy-optimizer/slothy/).

## Running the proofs

To reproduce the proofs, enter the nix shell via

```bash
nix develop --experimental-features 'nix-command flakes'
```

from mlkem-native's base directory. Then

```bash
make -C proofs/hol_light/arm
```

will build and run the proofs. Note that this make take hours even on powerful machines.

For convenience, you can also use `tests hol_light` which wraps the `make` invocation above; see `tests hol_light --help`.

### macOS (AArch64)

If you want run the proofs from an AArch64 Apple machine, you need to manually install `gobjcopy` via

```
brew install binutils
```

and put its parent directory (typically `/opt/homebrew/opt/binutils/bin`) into your `PATH`.
This is needed to convert Mach-O object files to ELF (if you know a way to install a suitable version
of `objcopy` through `nix`, please let us know!).
