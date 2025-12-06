[//]: # (SPDX-License-Identifier: CC-BY-4.0)

# Multi-Level Build (Native Backend)

This directory contains a minimal example for building mlkem-native with support for all three security levels
(ML-KEM-512, ML-KEM-768, ML-KEM-1024), using native backends for optimal performance, with level-independent
code shared to reduce binary size.

## Use Case

Use this approach when:
- You need multiple ML-KEM security levels in the same application
- You want optimal performance via native assembly (AArch64/AVX2)
- You want to build the mlkem-native C files separately, not as a single compilation unit.
- You want to minimize code duplication across levels

## Components

1. mlkem-native source tree: [`mlkem/src/`](../../mlkem/src), [`mlkem/src/fips202/`](../../mlkem/src/fips202),
   and [`mlkem/src/native/`](../../mlkem/src/native)
2. A secure random number generator implementing [`randombytes.h`](../../mlkem/src/randombytes.h)
3. Your application source code

## Configuration

The library is built 3 times into separate directories (`build/mlkem512`, `build/mlkem768`, `build/mlkem1024`).

The configuration file [mlkem_native_config.h](mlkem_native/mlkem_native_config.h) sets:
- `MLK_CONFIG_MULTILEVEL_BUILD`: Enables multi-level build mode
- `MLK_CONFIG_NAMESPACE_PREFIX=mlkem`: Base prefix; level suffix added automatically
- `MLK_CONFIG_USE_NATIVE_BACKEND_ARITH`: Enables native arithmetic backend
- `MLK_CONFIG_USE_NATIVE_BACKEND_FIPS202`: Enables native FIPS-202 backend

Build-time flags passed via CFLAGS:
- `MLK_CONFIG_PARAMETER_SET=512/768/1024`: Selects the security level
- `MLK_CONFIG_MULTILEVEL_WITH_SHARED`: Set for ONE build to include shared code
- `MLK_CONFIG_MULTILEVEL_NO_SHARED`: Set for OTHER builds to exclude shared code

The resulting API functions are namespaced as:
- `mlkem512_keypair()`, `mlkem512_enc()`, `mlkem512_dec()`
- `mlkem768_keypair()`, `mlkem768_enc()`, `mlkem768_dec()`
- `mlkem1024_keypair()`, `mlkem1024_enc()`, `mlkem1024_dec()`

## Notes

- Native backends are auto-selected based on the target architecture
- On unsupported platforms, the build falls back to the C backend

## Usage

```bash
make build   # Build all three security levels
make run     # Run the example
```

## Warning

The `randombytes()` implementation in `test_only_rng/` is for TESTING ONLY.
You MUST provide a cryptographically secure RNG for production use.
