[//]: # (SPDX-License-Identifier: CC-BY-4.0)

# mlkem-native AArch64 backend SLOTHY-optimized code

This directory contains the AArch64 backend _after_ it has
been optimized by SLOTHY.

## Running SLOTHY from the Makefile

If the "clean" backend sources in [`../../aarch64_clean/src/*.S`](../../aarch64_clean/src/) change,
then the `Makefile` in this directory can be used to re-generate the
optimized sources using SLOTHY.

The Makefile requires you to have a working SLOTHY setup. Note that mlkem-native's nix shell does currently not include SLOTHY.
See the [SLOTHY Readme](https://github.com/slothy-optimizer/slothy/) for more details.

## Example set up on macOS

On macOS, let's say we have SLOTHY installed below
$SLOTHY_ROOT, the mlkem-native repo in $MLKEM_NATIVE_ROOT, and llvm-mc in /opt/homebrew/opt/llvm/bin,
then

```
cd $SLOTHY_ROOT
# Force Python 3.11
pyenv local 3.11
# Start the python venv
source venv/bin/activate

# Add slothy-cli and llvm-mc to PATH
PATH=$SLOTHY_ROOT:/opt/homebrew/opt/llvm/bin:$PATH
export PATH

# Goto mlkem-native repo
cd $MLKEM_NATIVE_ROOT
cd dev/aarch64_opt/src
make
```

should apply SLOTHY to whatever clean assembly sources require processing.

Do
```
make -B all
```
to process all the sources.

To transfer the newly optimized files into the main source tree [mlkem/native](../../../mlkem/native), run `autogen` from the `nix` shell.

## Current exceptions - file not processed by SLOTHY

At present, `rej_uniform_asm.S` is not passed through SLOTHY, owing to complexity
in its control flow. The Makefile simply copies this file from the "clean" directory unmodified.

An additional target in the Makefile called
`rej_uniform_asm_with_slothy.S` can be used to force SLOTHY to run on these units. This
can be used to test SLOTHY as and when SLOTHY can process it.
