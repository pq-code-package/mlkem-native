[//]: # (SPDX-License-Identifier: CC-BY-4.0)

# Single-level mlkem-native in a single compilation unit

This directory contains a minimal example for how to build a single instance of mlkem-native with native backend,
using a single C compilation unit and a single assembly ile.

The auto-generated source file [mlkem_native_monobuild.c](mlkem_native_monobuild.c) includes all mlkem-native C source
files. Moreover, it clears all `#define`s clauses set by mlkem-native at the end, and is hence amenable to multiple
inclusion in another compilation unit. It exposes the API [../../mlkem/mlkem_native.h](../../mlkem/mlkem_native.h).

Similarly, the auto-generated source file [mlkem_native_monobuild.S](mlkem_native_monobuild.S) includes all mlkem-native
assembly source files files.

## Usage

Build this example with `make build`, run with `make run`.

**WARNING:** The `randombytes()` implementation used here is for TESTING ONLY. You MUST NOT use this implementation
outside of testing.
