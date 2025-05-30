[//]: # (SPDX-License-Identifier: CC-BY-4.0)

# Using mlkem-native as a code package

This directory contains a minimal example for how to use mlkem-native as a code package, without modifications.

## Components

An application using mlkem-native as-is needs to include the following components:

1. mlkem-native source tree, including [`mlkem/src/`](../../mlkem/src) and [`mlkem/src/fips202/`](../../mlkem/src/fips202).
2. A secure pseudo random number generator, implementing [`randombytes.h`](../../mlkem/src/randombytes.h).
3. The application source code

**WARNING:** The `randombytes()` implementation used here is for TESTING ONLY. You MUST NOT use this implementation
outside of testing.

## Usage

Build this example with `make build`, run with `make run`.
