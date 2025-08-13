[//]: # (SPDX-License-Identifier: CC-BY-4.0)

# Multi-level build with no standard library

This directory contains a minimal example for how to build mlkem-native with support for all 3 security levels
MLKEM-512, MLKEM-768, and MLKEM-1024, and so that level-independent code is shared. In this example, only the C-backend
of mlkem-native is used.

The library is built 3 times in different build directories `build/mlkem{512,768,1024}`. For the MLKEM-512 build, we set
`MLK_CONFIG_MULTILEVEL_WITH_SHARED` to force the inclusion of all level-independent code in the
MLKEM512-build. For MLKEM-768 and MLKEM-1024, we set `MLK_CONFIG_MULTILEVEL_NO_SHARED` to not include any
level-independent code, beside this, this example replace the `mlk_memcpy`, `mlk_memset` with the custom implementation memcpy and memset instead of using the stdlib by adding `example_no_stdlib_config.h`, and add the `-nostdlib` during objects file building,
Finally, we use the common namespace prefix `mlkem` as `MLK_CONFIG_NAMESPACE_PREFIX` for all three builds; 
the suffix 512/768/1024 will be added to level-dependent functions automatically.

## Usage

Build this example with `make build`, run with `make run`.
