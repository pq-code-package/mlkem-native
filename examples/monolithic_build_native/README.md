[//]: # (SPDX-License-Identifier: CC-BY-4.0)

# Monolithic Build (Native Backend)

This directory contains a minimal example for building mlkem-native as a single compilation unit
with native assembly backends, using the auto-generated `mlkem_native.c` and `mlkem_native.S` files.

## Use Case

Use this approach when:
- You need only one ML-KEM parameter set (512, 768, or 1024)
- You want simple build integration with optimal performance

## Components

1. Source tree [mlkem_native/*](mlkem_native), including top-level compilation unit
   [mlkem_native.c](mlkem_native/mlkem_native.c) (gathering all C sources),
   [mlkem_native.S](mlkem_native/mlkem_native.S) (gathering all assembly sources),
   and the mlkem-native API [mlkem_native.h](mlkem_native/mlkem_native.h).
2. A secure random number generator implementing [`randombytes.h`](../../mlkem/src/randombytes.h)
3. Your application source code

## Configuration

The configuration file [mlkem_native_config.h](mlkem_native/mlkem_native_config.h) sets:
- `MLK_CONFIG_PARAMETER_SET`: Security level (default 768)
- `MLK_CONFIG_NAMESPACE_PREFIX`: Symbol prefix (set to `mlkem`)
- `MLK_CONFIG_USE_NATIVE_BACKEND_ARITH`: Enables native arithmetic backend
- `MLK_CONFIG_USE_NATIVE_BACKEND_FIPS202`: Enables native FIPS-202 backend

## Notes

- Both `mlkem_native.c` and `mlkem_native.S` must be compiled and linked
- Native backends are auto-selected based on target architecture
- On unsupported platforms, the C backend is used automatically

## Usage

```bash
make build   # Build the example
make run     # Run the example
```

## Warning

The `randombytes()` implementation in `test_only_rng/` is for TESTING ONLY.
You MUST provide a cryptographically secure RNG for production use.
