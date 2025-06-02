[//]: # (SPDX-License-Identifier: CC-BY-4.0)

# Single-level mlkem-native in a single compilation unit, with native code

This directory contains a minimal example for how to build a single instance of mlkem-native in a single compilation
unit, including the native backends.

The auto-generated source file [mlkem_native.c](mlkem/mlkem_native.c) includes all mlkem-native C source
files. Similarly, [mlkem_native.S](mlkem/mlkem_native.S) includes all assembly files.
It exposes the API [mlkem/mlkem_native.h](mlkem/mlkem_native.h).

## Usage

Build this example with `make build`, run with `make run`.

**WARNING:** The `randombytes()` implementation used here is for TESTING ONLY. You MUST NOT use this implementation
outside of testing.
