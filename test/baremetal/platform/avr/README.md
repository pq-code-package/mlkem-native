[//]: # (SPDX-License-Identifier: CC-BY-4.0)

# AVR baremetal build environment

This directory provides a baremetal build and test environment for AVR MCUs, using `avr-gcc` for compiling and `simavr` for emulation.

This is primarily a vehicle to test that mlkem-native builds and is functionally correct in 16-bit C implementations. For actual practical use on 16-bit MCUs, stack usage would need to be reduced.

**Note:** We currently need close to the full 64K data address space of the AVR architecture, more than any MCU supported by `simavr`; we therefore use a patched version of `simavr` where Atmega128rfr2 is given 63.5K of RAM (0x0200-0xFFFF). To test this, you must work in the `nix .#cross-avr` shell specified in nix flake.
