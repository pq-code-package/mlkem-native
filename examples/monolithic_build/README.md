[//]: # (SPDX-License-Identifier: CC-BY-4.0)

# Single-level mlkem-native in a single compilation unit

This directory contains a minimal example for how to build a single instance of mlkem-native in a single compilation
unit. Only the C-backend is exercised.

The auto-generated source file [mlkem_native.c](mlkem_native/mlkem_native.c) includes all mlkem-native C source
files. Moreover, it clears all `#define`s clauses set by mlkem-native at the end, and is hence amenable to multiple
inclusion in another compilation unit. It exposes the API [mlkem_native.h](mlkem_native/mlkem_native.h).

The configuration file [mlkem_native_config.h](mlkem_native/mlkem_native_config.h) sets
`MLK_CONFIG_INTERNAL_API_QUALIFIER` to `static`, making all internal functions static for the single-CU build.

## Usage

Build this example with `make build`, run with `make run`.

**WARNING:** The `randombytes()` implementation used here is for TESTING ONLY. You MUST NOT use this implementation
outside of testing.
