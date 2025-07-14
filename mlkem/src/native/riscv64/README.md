[//]: # (SPDX-License-Identifier: CC-BY-4.0)

# RISC-V Vector Extension Backend

Notes on RISC-V Vector support.

**WARNING** This is highly experimental. Currently vlen=256 only.

## Implementation Status

This implementation is inferior to the AArch64 and AVX2 backends in the following ways:

- **Verification**: No formal verification has been performed on this backend
- **Testing**: Uses the same functional tests as AVX2 and AArch64 backends, but lacks extensive real-hardware testing
- **Audit**: This is new code that has not yet received thorough review or widespread use in production environments

## Requirements

- RISC-V 64-bit architecture
- Vector extension (RVV) version 1.0
- Minimum vector length (VLEN) of 256 bits
- Standard "gc" extensions (integer and compressed instructions)

