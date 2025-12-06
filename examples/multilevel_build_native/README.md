[//]: # (SPDX-License-Identifier: CC-BY-4.0)

# Multi-level build

This directory contains a minimal example for how to build mlkem-native with support for all 3 security levels
MLKEM-512, MLKEM-768, and MLKEM-1024. All level-independent code is shared, and native backends are in use.

The library is built 3 times in different build directories `build/mlkem{512,768,1024}`. The configuration file
[mlkem_native_config.h](mlkem_native/mlkem_native_config.h) sets `MLK_CONFIG_MULTILEVEL_BUILD` and
`MLK_CONFIG_NAMESPACE_PREFIX=mlkem`; the suffix 512/768/1024 will be added to level-dependent functions automatically.

For the MLKEM-512 build, we pass `MLK_CONFIG_MULTILEVEL_WITH_SHARED` via CFLAGS to force the inclusion of all
level-independent code. For MLKEM-768 and MLKEM-1024, we pass `MLK_CONFIG_MULTILEVEL_NO_SHARED` to exclude
level-independent code. The parameter set `MLK_CONFIG_PARAMETER_SET` is also passed via CFLAGS for each build.

## Usage

Build this example with `make build`, run with `make run`.
