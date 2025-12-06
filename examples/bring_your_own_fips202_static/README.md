[//]: # (SPDX-License-Identifier: CC-BY-4.0)

# Bring Your Own FIPS-202 (Static State Variant)

This directory contains a minimal example for using mlkem-native with a custom FIPS-202 implementation
that uses a single global state. This is common for hardware accelerators that can only hold one
Keccak state at a time.

## Use Case

Use this approach when:
- Your application already has a FIPS-202 software/hardware implementation you want to reuse
- Your FIPS-202 implementation does not support multiple active SHA3/SHAKE computations.

## Components

1. Arithmetic part of mlkem-native: [`mlkem/src/`](../../mlkem/src) (excluding `fips202/`)
2. A secure random number generator implementing [`randombytes.h`](../../mlkem/src/randombytes.h)
3. Custom FIPS-202 implementation with header compatible with [`fips202.h`](../../mlkem/src/fips202/fips202.h)
4. Stub `fips202x4.h` header (the 4x functions are unused in this mode)
5. Your application source code

## Configuration

The configuration file [mlkem_native_config.h](mlkem_native/mlkem_native_config.h) sets:
- `MLK_CONFIG_SERIAL_FIPS202_ONLY`: Disables batched Keccak; matrix entries generated one at a time
- `MLK_CONFIG_FIPS202_CUSTOM_HEADER`: Path to your custom `fips202.h`
- `MLK_CONFIG_FIPS202X4_CUSTOM_HEADER`: Path to stub `fips202x4.h`

Your custom FIPS-202 implementation must provide:
- `mlk_shake128_absorb_once()`, `mlk_shake128_squeezeblocks()`, `mlk_shake128_release()`
- `mlk_shake256()`, `mlk_sha3_256()`, `mlk_sha3_512()`
- Structure definition for `mlk_shake128ctx`

The `fips202x4.h` header can contain stubs since the 4x functions are never called.

## Notes

- `MLK_CONFIG_SERIAL_FIPS202_ONLY` may reduce performance on CPUs with SIMD support
- Matrix generation becomes sequential instead of batched (4 entries at a time)
- Only enable this when your hardware requires it

## Usage

```bash
make build   # Build the example
make run     # Run the example
```

## Warning

The `randombytes()` implementation in `test_only_rng/` is for TESTING ONLY.
You MUST provide a cryptographically secure RNG for production use.

<!--- bibliography --->
[^tiny_sha3]: Markku-Juhani O. Saarinen: tiny_sha3, [https://github.com/mjosaarinen/tiny_sha3](https://github.com/mjosaarinen/tiny_sha3)
