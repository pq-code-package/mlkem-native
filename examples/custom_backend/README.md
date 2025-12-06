[//]: # (SPDX-License-Identifier: CC-BY-4.0)

# Custom FIPS-202 Backend

This directory contains a minimal example for using mlkem-native with a custom FIPS-202 *backend*
(as opposed to a complete custom FIPS-202 implementation). We use tiny_sha3[^tiny_sha3] as an example.

## Use Case

Use this approach when:
- You want to replace the low-level Keccak-f1600 permutation
- You want to keep mlkem-native's FIPS-202 frontend (absorb/squeeze logic)

This differs from `bring_your_own_fips202` in that you only replace the *backend* (Keccak permutation),
not the entire FIPS-202 implementation.

## Components

1. Arithmetic part of mlkem-native: [`mlkem/src/`](../../mlkem/src)
2. FIPS-202 frontend: [`mlkem/src/fips202/`](../../mlkem/src/fips202) (can remove existing backends)
3. A secure random number generator implementing [`randombytes.h`](../../mlkem/src/randombytes.h)
4. Custom FIPS-202 backend (see below)
5. Your application source code

## Configuration

The configuration file [mlkem_native_config.h](mlkem_native/mlkem_native_config.h) sets:
- `MLK_CONFIG_USE_NATIVE_BACKEND_FIPS202`: Enables native FIPS-202 backend
- `MLK_CONFIG_FIPS202_BACKEND_FILE`: Path to your custom backend metadata file

A custom backend consists of:
1. A metadata header (e.g., [custom.h](mlkem_native/src/fips202/native/custom/custom.h)) that:
   - Sets `MLK_USE_FIPS202_X1_NATIVE` (and/or `X2`/`X4`) to indicate which functions are replaced
   - Includes the implementation header
2. An implementation providing `mlk_keccakf1600_native()` (and/or batched variants)

Example backend metadata file:
```c
#ifndef CUSTOM_FIPS202_BACKEND_H
#define CUSTOM_FIPS202_BACKEND_H

/* Indicate we're replacing 1-fold Keccak-f1600 */
#define MLK_USE_FIPS202_X1_NATIVE

/* Include the implementation */
#include "custom/src/keccak_impl.h"

#endif
```

## Notes

- The tiny_sha3 code uses byte-reversed Keccak state on big-endian targets; this example removes
  that reversal since mlkem-native's frontend assumes standard byte order

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
