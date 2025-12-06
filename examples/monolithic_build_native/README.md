[//]: # (SPDX-License-Identifier: CC-BY-4.0)

# Monolithic Build (Native Backend)

This directory contains a minimal example for building mlkem-native as a single compilation unit
with native assembly backends, using the auto-generated `mlkem_native.c` and `mlkem_native.S` files.

## Use Case

Use this approach when:
- You want simple build integration with optimal performance
- You need only one parameter set

## Components

1. Auto-generated [mlkem_native.c](mlkem_native/mlkem_native.c) (includes all C sources)
2. Auto-generated [mlkem_native.S](mlkem_native/mlkem_native.S) (includes all assembly sources)
3. A secure random number generator implementing [`randombytes.h`](../../mlkem/src/randombytes.h)
4. Your application source code

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
