[//]: # (SPDX-License-Identifier: CC-BY-4.0)

# Bring your own FIPS-202 (Static State Variant)

This directory contains a minimal example for how to use mlkem-native with external FIPS202
HW/SW-implementations that use a single global state (for example, some hardware accelerators).
Specifically, this example demonstrates the use of the serial-only FIPS-202 configuration
`MLK_CONFIG_SERIAL_FIPS202_ONLY`.

## Components

An application using mlkem-native with a custom FIPS-202 implementation needs the following:

1. Arithmetic part of the mlkem-native source tree: [`mlkem/src/`](../../mlkem/src)
2. A secure pseudo random number generator, implementing [`randombytes.h`](../../mlkem/src/randombytes.h).
2. A custom FIPS202 with `fips202.h` header compatible with [`mlkem/src/fips202/fips202.h`](../../mlkem/src/fips202/fips202.h).
   The FIPS202x4 header `fips202x4.h` can is unused with `MLK_CONFIG_SERIAL_FIPS202_ONLY` and can be filled with stubs.
3. The application source code

**WARNING:** The `randombytes()` implementation used here is for TESTING ONLY. You MUST NOT use this implementation
outside of testing.

## Usage

Build this example with `make build`, run with `make run`.

<!--- bibliography --->
[^tiny_sha3]: Markku-Juhani O. Saarinen: tiny_sha3, [https://github.com/mjosaarinen/tiny_sha3](https://github.com/mjosaarinen/tiny_sha3)
