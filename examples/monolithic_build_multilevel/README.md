[//]: # (SPDX-License-Identifier: CC-BY-4.0)

# Monolithic Multi-Level Build (C Backend)

This directory contains a minimal example for building all three ML-KEM security levels in a single
compilation unit, with shared code deduplicated.

## Use Case

Use this approach when:
- You need all ML-KEM security levels in one application
- You want the simplest possible multi-level integration (one `.c` file)
- You're using only C (no native backend)

## Components

An application using mlkem-native as a monolithic multi-level build needs:

1. Source tree [mlkem_native/*](mlkem_native), including top-level compilation unit
   [mlkem_native.c](mlkem_native/mlkem_native.c) (gathering all C sources)
   and the mlkem-native API [mlkem_native.h](mlkem_native/mlkem_native.h).
2. Manually provided wrapper file [mlkem_native_all.c](mlkem_native_all.c),
   including `mlkem_native.c` three times.
3. Manually provided header file [mlkem_native_all.h](mlkem_native_all.h),
   including `mlkem_native.h` three times)
4. A secure random number generator implementing [`randombytes.h`](../../mlkem/src/randombytes.h)
5. Your application source code

## Configuration

The configuration file [mlkem_native_config.h](mlkem_native/mlkem_native_config.h) sets:
- `MLK_CONFIG_MULTILEVEL_BUILD`: Enables multi-level mode
- `MLK_CONFIG_NAMESPACE_PREFIX=mlkem`: Base prefix
- `MLK_CONFIG_INTERNAL_API_QUALIFIER=static`: Makes internal functions static

The wrapper [mlkem_native_all.c](mlkem_native_all.c) includes `mlkem_native.c` three times:
```c
#define MLK_CONFIG_FILE "multilevel_config.h"

/* Include level-independent code with first level */
#define MLK_CONFIG_MULTILEVEL_WITH_SHARED
#define MLK_CONFIG_MONOBUILD_KEEP_SHARED_HEADERS
#define MLK_CONFIG_PARAMETER_SET 512
#include "mlkem_native.c"
#undef MLK_CONFIG_PARAMETER_SET
#undef MLK_CONFIG_MULTILEVEL_WITH_SHARED

/* Exclude level-independent code for subsequent levels */
#define MLK_CONFIG_MULTILEVEL_NO_SHARED
#define MLK_CONFIG_PARAMETER_SET 768
#include "mlkem_native.c"
#undef MLK_CONFIG_PARAMETER_SET
#undef MLK_CONFIG_MONOBUILD_KEEP_SHARED_HEADERS

#define MLK_CONFIG_PARAMETER_SET 1024
#include "mlkem_native.c"
#undef MLK_CONFIG_PARAMETER_SET
```

The header [mlkem_native_all.h](mlkem_native_all.h) exposes all APIs:
```c
#define MLK_CONFIG_NO_SUPERCOP

#define MLK_CONFIG_PARAMETER_SET 512
#include <mlkem_native.h>
#undef MLK_CONFIG_PARAMETER_SET
#undef MLK_H

#define MLK_CONFIG_PARAMETER_SET 768
#include <mlkem_native.h>
#undef MLK_CONFIG_PARAMETER_SET
#undef MLK_H

#define MLK_CONFIG_PARAMETER_SET 1024
#include <mlkem_native.h>
#undef MLK_CONFIG_PARAMETER_SET
#undef MLK_H
```

## Notes

- `MLK_CONFIG_MULTILEVEL_WITH_SHARED` must be set for exactly ONE level
- `MLK_CONFIG_MONOBUILD_KEEP_SHARED_HEADERS` prevents cleanup of shared headers between inclusions
- `MLK_CONFIG_NO_SUPERCOP` is required to avoid conflicting `CRYPTO_*` macro definitions

## Usage

```bash
make build   # Build the example
make run     # Run the example
```

## Warning

The `randombytes()` implementation in `test_only_rng/` is for TESTING ONLY.
You MUST provide a cryptographically secure RNG for production use.
