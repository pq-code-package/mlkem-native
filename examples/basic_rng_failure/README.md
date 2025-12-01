[//]: # (SPDX-License-Identifier: CC-BY-4.0)

# Building mlkem-native

This directory contains a minimal example for how to build mlkem-native and
intentionally force failures in the `randombytes` provider so that you can
exercise the library’s error paths.

## Components

An application using mlkem-native as-is needs to include the following components:

1. mlkem-native source tree, including [`mlkem/src/`](../../mlkem/src) and [`mlkem/src/fips202/`](../../mlkem/src/fips202).
2. A secure pseudo random number generator, implementing [`randombytes.h`](../../mlkem/src/randombytes.h).
3. The application source code

**WARNING:** The `randombytes()` implementation used here is for TESTING ONLY. You MUST NOT use this implementation
outside of testing.

## Usage

Build this example with `make build`, run with `make run`.

The test binary executes three scenarios for each security level:

1. Force the first `randombytes` invocation (during key generation) to fail and
	check that `crypto_kem_keypair` returns -1.
2. Allow key generation, then fail the second `randombytes` invocation (during
	signing) and confirm `crypto_kem_enc` returns -1.
3. Disable failure injection (negative index) and exercise the full
	sign/verify flow, ensuring the expected deterministic signature is produced.
