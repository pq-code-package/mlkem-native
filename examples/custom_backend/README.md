[//]: # (SPDX-License-Identifier: CC-BY-4.0)

# Using a custom configuration and FIPS-202 backend

This directory contains a minimal example for how to use mlkem-native as a code package, with a custom FIPS-202
backend and a custom configuration. We use [^tiny_sha3] as an example.

## Components

An application using mlkem-native with a custom FIPS-202 backend and custom configuration needs the following:

1. Arithmetic part of the mlkem-native source tree: [`mlkem/`](../../mlkem). In this example, we disable arithmetic
   backends, hence it is safe to remove the entire `native` subfolder.
2. A secure pseudo random number generator, implementing [`randombytes.h`](../../mlkem/randombytes.h). **WARNING:** The
   `randombytes()` implementation used here is for TESTING ONLY. You MUST NOT use this implementation outside of testing.
3. FIPS-202 part of the mlkem-native source tree, [`fips202/`](../../mlkem/fips202). If you only want to use your backend,
   you can remove all existing backends; that's what this example does.
4. A custom FIPS-202 backend. In this example, the backend file is
   [custom.h](mlkem_native/mlkem/fips202/native/custom/custom.h), wrapping
   [sha3.c](mlkem_native/mlkem/fips202/native/custom/src/sha3.c) and setting `MLK_USE_FIPS101_X1_NATIVE` to indicate that we
   replace 1-fold Keccak-F1600.
5. Either modify the existing [config.h](mlkem_native/mlkem/config.h), or register a new config. In this example, we add
   a new config [custom_config.h](mlkem_native/custom_config.h) and register it from the command line for
   `-DMLK_CONFIG_FILE="custom_config.h"` -- no further changes to the build are needed. For the sake of
   demonstration, we set a custom namespace. We set `MLK_FIPS202_BACKEND` to point to our custom FIPS-202
   backend, but leave `MLK_ARITH_BACKEND` undefined to indicate that we wish to use the C backend.

## Note

The tiny_sha3 code uses a byte-reversed presentation of the Keccakf1600 state for big-endian targets. Since
mlkem-native's FIPS202 frontend assumes a standard presentation, the corresponding byte-reversal in
[sha3.c](mlkem_native/mlkem/fips202/native/custom/src/sha3.c) is removed.

## Usage

Build this example with `make build`, run with `make run`.

<!--- bibliography --->
[^tiny_sha3]: Markku-Juhani O. Saarinen: tiny_sha3, [https://github.com/mjosaarinen/tiny_sha3](https://github.com/mjosaarinen/tiny_sha3)
