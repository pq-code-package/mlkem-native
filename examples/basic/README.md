[//]: # (SPDX-License-Identifier: CC-BY-4.0)

# Basic build

This directory contains a minimal example for how to build mlkem-native for a single security level.

## Use Case

Use this approach when:
- You need only one ML-KEM security level (512, 768, or 1024)
- You want to build the mlkem-native C files separately, not as a single compilation unit.
- You're using C only, no native backends.

## Components

1. mlkem-native source tree: [`mlkem/src/`](../../mlkem/src) and [`mlkem/src/fips202/`](../../mlkem/src/fips202)
2. A secure random number generator implementing [`randombytes.h`](../../mlkem/src/randombytes.h)
3. Your application source code

## Configuration

The configuration file [mlkem_native_config.h](mlkem_native/mlkem_native_config.h) sets:
- `MLK_CONFIG_PARAMETER_SET`: Security level (512, 768, or 1024). Default is 768.
- `MLK_CONFIG_NAMESPACE_PREFIX`: Symbol prefix for the API. Set to `mlkem` in this example.

To change the security level, modify `MLK_CONFIG_PARAMETER_SET` in the config file or pass it via CFLAGS:
```bash
make build CFLAGS="-DMLK_CONFIG_PARAMETER_SET=512"
```

## Usage

```bash
make build   # Build the example
make run     # Run the example
```

## Warning

The `randombytes()` implementation in `test_only_rng/` is for TESTING ONLY.
You MUST provide a cryptographically secure RNG for production use.
