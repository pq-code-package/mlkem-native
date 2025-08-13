[//]: # (SPDX-License-Identifier: CC-BY-4.0)

# Multi-level build with no standard library

This directory contains a minimal example demonstrating how to build mlkem-native with support for all three security levels: MLKEM-512, MLKEM-768, and MLKEM-1024, and so that level-independent code is shared. Unlike a simple [`multilevel_build`](../multilevel_build/README.md), this example also demonstrates how to replace `mlk_memcpy` and `mlk_memset` with custom implementations, allowing the build to proceed without using the standard library (stdlib).
In this example, only the C-backend of mlkem-native is used.

The library is built 3 times in different build directories `build/mlkem{512,768,1024}`. For the MLKEM-512 build, we set
`MLK_CONFIG_MULTILEVEL_WITH_SHARED` to force the inclusion of all level-independent code in the
MLKEM512-build. For ML-KEM-768 and ML-KEM-1024, we set `MLK_CONFIG_MULTILEVEL_NO_SHARED` to not include any
level-independent code, beside this, this example replace the `mlk_memcpy`, `mlk_memset` with the custom implementation memcpy and memset instead of using the stdlib by adding `example_no_stdlib_config.h`, and add `-nostdlib` to the compilation flags,
Finally, we use the common namespace prefix `mlkem` as `MLK_CONFIG_NAMESPACE_PREFIX` for all three builds; 
the suffix 512/768/1024 will be added to level-dependent functions automatically.

## Usage

Build this example with `make build`, run with `make run`.
