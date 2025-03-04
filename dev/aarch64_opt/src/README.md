[//]: # (SPDX-License-Identifier: CC-BY-4.0)

# mlkem-native AArch64 back-end SLOTHY-optimized code

This directory contains the AArch64 back-end _after_ it has
been optimized by SLOTHY.

## Running SLOTHY from the Makefile

If the "clean" back-end sources in `../../aarch64_clean/src/*.S` change,
then the `Makefile` in this directory can be used to re-generate the
optimized sources using SLOTHY.

The Makefile requires a _particular_ set up. In short:

1. Do NOT run from within the NIX environment.
2. You must have Python 3.11 on PATH (3.12 does not work at present)
3. You must have the LLVM tool `llvm-mc` on PATH.
4. You must have the slothy-cli on PATH.
5. You must start the SLOTHY Python virtual-environment.

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

## Current exceptions - file not processed by SLOTHY

At present, 2 of the "clean" assembly files are not passed through SLOTHY, owing to
instructions that SLOTHY does not support.  These files
are

```
rej_uniform_asm.S
poly_tobytes_asm.S
```

The Makefile simply copies these files from the "clean" directory unmodified.

Additional targets are contained in the Makefile called `poly_tobytes_asm_with_slothy.S` and
`rej_uniform_asm_with_slothy.S` that can be use to force SLOTHY to run on these units. These
can be used to test SLOTHY as and when the missing instructions are added.
