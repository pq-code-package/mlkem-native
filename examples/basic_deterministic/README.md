[//]: # (SPDX-License-Identifier: CC-BY-4.0)

# Building mlkem-native

This directory contains a minimal example showing how to build **mlkem-native** for use cases only requiring the deterministic key generation and encapsulation APIs (`crypto_kem_keypair_derand` and `crypto_kem_enc_derand`). In that case, no implementation of `randombytes()` has to be provided.

The configuration file [mlkem_native_config.h](mlkem_native/mlkem_native_config.h) sets `MLK_CONFIG_NO_RANDOMIZED_API`
to disable the randomized API functions.

## Components

An application using mlkem-native as-is needs to include the following components:

1. mlkem-native source tree, including [`mlkem/src/`](../../mlkem/src) and [`mlkem/src/fips202/`](../../mlkem/src/fips202).
2. The application source code


## Usage

Build this example with `make build`, run with `make run`.
