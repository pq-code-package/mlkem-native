[//]: # (SPDX-License-Identifier: CC-BY-4.0)

# Usage examples

This directory contains minimal examples demonstrating how to use mlkem-native.

## Using unmodified mlkem-native as a code package

See [mlkem_native_as_code_package](mlkem_native_as_code_package).

## Using mlkem-native as a code package, bring your own FIPS-202

See [bring_your_own_fips202](bring_your_own_fips202) for an example of how to use mlkem-native with your own FIPS-202
implementation.

## Using mlkem-native as a code package, custom config + custom FIPS-202 backend

See [custom_backend](custom_backend) for an example of how to use mlkem-native with a custom configuration file and a
custom FIPS-202 backend.

## Building mlkem-native with a single compilation unit

See [monolithic_build](monolithic_build) for an example of how to build mlkem-native (with C backend) from a single
auto-generated compilation unit.

## Multi-level mlkem-native inside a single compilation unit

See [monolithic_build_multilevel](monolithic_build_multilevel) for an example of how to build all security levels of
mlkem-native (with C backend) inside a single compilation unit, sharing the level-independent code.
