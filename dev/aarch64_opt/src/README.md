[//]: # (SPDX-License-Identifier: CC-BY-4.0)

# mlkem-native AArch64 backend SLOTHY-optimized code

This directory contains the AArch64 backend after it has been optimized by [SLOTHY](https://github.com/slothy-optimizer/slothy/).

## Re-running SLOTHY

If the "clean" sources [`../../aarch64_clean/src/*.S`](../../aarch64_clean/src/) change, take the following steps to re-optimize and install them into the main source tree:

1. Run `make` to re-generate the optimized sources using SLOTHY. This assumes a working SLOTHY setup, as established e.g. by the default nix shell for mlkem-native. See also the [SLOTHY README](https://github.com/slothy-optimizer/slothy/).

2. Run `autogen` to transfer the newly optimized files into the main source tree [mlkem/src/native](../../../mlkem/src/native).

3. Run `tests all --opt=OPT` to check that that the new assembly is still functional.

Note: By default, [rej_uniform_asm.S](rej_uniform_asm.S) is not passed through SLOTHY: The Makefile simply copies this file from the "clean" directory unmodified. The target `rej_uniform_asm_with_slothy.S` can be used to force SLOTHY to run on this file. This can be used to test SLOTHY as and when SLOTHY can process it.
