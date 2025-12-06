[//]: # (SPDX-License-Identifier: CC-BY-4.0)

# Monolithic Multi-Level Build (Native Backend)

This directory contains a minimal example for building all three ML-KEM security levels in a single
compilation unit with native assembly backends, with shared code deduplicated.

## Use Case

Use this approach when:
- You need all ML-KEM security levels in one application
- You want optimal performance via native assembly (AArch64/AVX2)
- You want maximum code sharing and LTO optimization
- You want the simplest possible multi-level native integration

## Components

1. Auto-generated [mlkem_native.c](mlkem_native/mlkem_native.c) (includes all C sources)
2. Auto-generated [mlkem_native.S](mlkem_native/mlkem_native.S) (includes all assembly sources)
3. Wrapper file [mlkem_native_all.c](mlkem_native_all.c) (includes `mlkem_native.c` three times)
4. A secure random number generator implementing [`randombytes.h`](../../mlkem/src/randombytes.h)
5. Your application source code

## Configuration

The configuration file [multilevel_config.h](multilevel_config.h) sets:
- `MLK_CONFIG_MULTILEVEL_BUILD`: Enables multi-level mode
- `MLK_CONFIG_NAMESPACE_PREFIX=mlkem`: Base prefix
- `MLK_CONFIG_USE_NATIVE_BACKEND_ARITH`: Enables native arithmetic backend
- `MLK_CONFIG_USE_NATIVE_BACKEND_FIPS202`: Enables native FIPS-202 backend

The wrapper [mlkem_native_all.c](mlkem_native_all.c) includes `mlkem_native.c` three times:
```c
#define MLK_CONFIG_FILE "multilevel_config.h"

/* Include level-independent code with first level */
#define MLK_CONFIG_MULTILEVEL_WITH_SHARED 1
#define MLK_CONFIG_MONOBUILD_KEEP_SHARED_HEADERS
#define MLK_CONFIG_PARAMETER_SET 512
#include "mlkem_native.c"
#undef MLK_CONFIG_MULTILEVEL_WITH_SHARED
#undef MLK_CONFIG_PARAMETER_SET

/* Exclude level-independent code for subsequent levels */
#define MLK_CONFIG_MULTILEVEL_NO_SHARED
#define MLK_CONFIG_PARAMETER_SET 768
#include "mlkem_native.c"
#undef MLK_CONFIG_MONOBUILD_KEEP_SHARED_HEADERS
#undef MLK_CONFIG_PARAMETER_SET

#define MLK_CONFIG_PARAMETER_SET 1024
#include "mlkem_native.c"
#undef MLK_CONFIG_PARAMETER_SET
```

The application [main.c](main.c) embeds the wrapper and imports constants:
```c
#include "mlkem_native_all.c"

#define MLK_CONFIG_CONSTANTS_ONLY
#include <mlkem_native.h>
```

## Notes

- Both `mlkem_native_all.c` and `mlkem_native.S` must be compiled and linked
- `MLK_CONFIG_MULTILEVEL_WITH_SHARED` must be set for exactly ONE level
- `MLK_CONFIG_CONSTANTS_ONLY` imports size constants without function declarations
- Native backends are auto-selected based on target architecture

## Usage

```bash
make build   # Build the example
make run     # Run the example
```

## Warnings

**CRITICAL:** The `randombytes()` implementation in `test_only_rng/` is for TESTING ONLY.
You MUST provide a cryptographically secure RNG for production use.
