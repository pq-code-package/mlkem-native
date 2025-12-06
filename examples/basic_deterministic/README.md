[//]: # (SPDX-License-Identifier: CC-BY-4.0)

# Basic derandomized-only build

This directory contains a minimal example for building mlkem-native using only the deterministic API,
without requiring a `randombytes()` implementation.

## Use Case

Use this approach when:
- Your application manages its own entropy/randomness externally
- You only need `crypto_kem_keypair_derand` and `crypto_kem_enc_derand` (deterministic variants)

## Components

1. mlkem-native source tree: [`mlkem/src/`](../../mlkem/src) and [`mlkem/src/fips202/`](../../mlkem/src/fips202)
2. Your application source code

No `randombytes()` implementation is required.

## Configuration

The configuration file [mlkem_native_config.h](mlkem_native/mlkem_native_config.h) sets:
- `MLK_CONFIG_NO_RANDOMIZED_API`: Disables `crypto_kem_keypair` and `crypto_kem_enc`
- `MLK_CONFIG_PARAMETER_SET`: Security level (default 768)
- `MLK_CONFIG_NAMESPACE_PREFIX`: Symbol prefix (set to `mlkem`)

## Notes

- This is incompatible with `MLK_CONFIG_KEYGEN_PCT` (pairwise consistency test)

## Usage

```bash
make build   # Build the example
make run     # Run the example
```
