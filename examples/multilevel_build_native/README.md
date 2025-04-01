[//]: # (SPDX-License-Identifier: CC-BY-4.0)

# Multi-level build

This directory contains a minimal example for how to build mlkem-native with support for all 3 security levels
MLKEM-512, MLKEM-768, and MLKEM-1024. All level-independent code is shared, and native backends are in use.

The library is built 3 times in different build directories `build/mlkem{512,768,1024}`. For the MLKEM-512 build, we set
`MLK_MULTILEVEL_BUILD_WITH_SHARED` to force the inclusion of all level-independent code in the
MLKEM512-build. For MLKEM-768 and MLKEM-1024, we set `MLK_MULTILEVEL_BUILD_NO_SHARED` to not include any
level-independent code. Finally, we use the common namespace prefix `mlkem` as `MLK_NAMESPACE_PREFIX` for all three
builds; the suffix 512/768/1024 will be added to level-dependent functions automatically.

## Usage

Build this example with `make build`, run with `make run`.
