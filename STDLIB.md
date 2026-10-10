[//]: # (SPDX-License-Identifier: CC-BY-4.0)

# Standard Library Dependencies

mlkem-native has minimal dependencies on the C standard library. This document lists all stdlib functions used and configuration options for custom replacements.

## Dependencies

### Memory Functions
- **memcpy**: Used extensively for copying data structures, keys, and intermediate values
- **memset**: Used for zeroing state structures and buffers, including by the default implementation of `mlk_zeroize` for security-critical zeroing (followed by a compiler barrier). `mlk_zeroize` can be replaced separately via `MLK_CONFIG_CUSTOM_ZEROIZE`

### Debug Functions (MLKEM_DEBUG builds only)
- **fprintf**: Used in debug.c for error reporting to stderr
- **exit**: Used in debug.c to terminate on assertion failures

## Custom Replacements

Custom replacements can be provided for memory functions using the configuration options in `mlkem/mlkem_native_config.h`:

### MLK_CONFIG_CUSTOM_MEMCPY
Replaces all `memcpy` calls with a custom implementation. When enabled, you must define a `mlk_memcpy` function with the same signature as the standard `memcpy`.

### MLK_CONFIG_CUSTOM_MEMSET
Replaces all `memset` calls with a custom implementation. When enabled, you must define a `mlk_memset` function with the same signature as the standard `memset`.

See the configuration examples in `mlkem/mlkem_native_config.h` and test configurations in `test/configs/custom_*_config.h` for usage examples and implementation requirements.
