[//]: # (SPDX-License-Identifier: CC-BY-4.0)

# HOL Light functional correctness proofs

This directory contains functional correctness proofs for some optimized
ML-KEM AArch64 assembly routines. The proofs were developed by John Harrison
and are written in the [HOL Light](https://hol-light.github.io/) theorem
prover, utilizing the assembly verification infrastructure from [s2n-bignum](https://github.com/awslabs/s2n-bignum).

The HOL-Light proofs in this dircetory are not yet synchronized with the assembly in
[mlkem/native/aarch64/src](../../../mlkem/native/aarch64/src) -- we do not yet claim that the AArch64 NTT and invNTT
that mlkem-native ships with are formally verified.

Each function is proved in a separate `.ml` file in [proofs/](proofs). Each file
contains the byte code being verified, as well as the specification that is being
proved. Specifications are essentially Hoare triples, with the noteworthy difference
that the program is implicit as the content of memory at the PC; which is asserted to
be the code under verification as part of the precondition.

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

### macOS (AArch64)

If you want run the proofs from an AArch64 Apple machine, you need to manually install `gobjcopy` via

```
brew install binutils
```

and put its parent directory (typically `/opt/homebrew/opt/binutils/bin`) into your `PATH`.
This is needed to convert Mach-O object files to ELF (if you know a way to install a suitable version
of `objcopy` through `nix`, please let us know!).

## What is covered?

At present, this directory contains functional correctness proofs for the following functions:

- Optimized AArch64 forward NTT: [mlkem_ntt.S](mlkem/mlkem_ntt.S)
- Optimized AArch64 inverse NTT: [mlkem_intt.S](mlkem/mlkem_intt.S)

Both functions are super-optimized using [SLOTHY](https://github.com/slothy-optimizer/slothy/).
