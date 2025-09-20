[//]: # (SPDX-License-Identifier: CC-BY-4.0)

# Usage examples

This directory contains minimal examples demonstrating how you can use mlkem-native.

## Basic

See [basic](basic) for a basic example of how to build a single instance of mlkem-native.

## Basic_deterministic

See [basic_deterministic](basic_deterministic) for a basic example of how to build a single instance of mlkem-native without `randombytes()` implementation. This allows users to build mlkem-native using only the deterministic API when randomized functions are not required.
## Multi-level build (C only)

See [multilevel_build](multilevel_build) for an example of how to build one instance of mlkem-native per security level,
in such a way that level-independent code is shared.

## Multi-level build (with native code)

See [multilevel_build_native](multilevel_build_native) for an example of how to build one instance of mlkem-native per
security level, in such a way that level-independent code is shared, and leveraging the native backends.

## Custom FIPS202 implementation

See [bring_your_own_fips202](bring_your_own_fips202) for an example of how to use mlkem-native with your own FIPS-202
implementation.

## Custom config + custom FIPS-202 backend

See [custom_backend](custom_backend) for an example of how to use mlkem-native with a custom configuration file and a
custom FIPS-202 backend.

## Monobuild (C only)

See [monolithic_build](monolithic_build) for an example of how to build mlkem-native (with C backend) from a single
auto-generated compilation unit.

## Multi-level monobuild (C only)

See [monolithic_build_multilevel](monolithic_build_multilevel) for an example of how to build all security levels of
mlkem-native (with C backend) inside a single compilation unit, sharing the level-independent code.

## Multi-level monobuild (with native code)

See [monolithic_build_multilevel_native](monolithic_build_multilevel_native) for an example of how to build all security
levels of mlkem-native inside a single compilation unit, sharing the level-independent code, while also linking in assembly
from the native backends.
