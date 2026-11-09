[//]: # (SPDX-License-Identifier: CC-BY-4.0)

# RISC-V Vector Extension Backend

This is an arithmetic backend for CPUs implementing the RISC-V Vector Extension. The backend is functional for all physical `VLEN`, but the NTT and inverse NTT are so far only implemented for VLEN=128 and VLEN=256, falling back to the default C implementations for other VLENs.

## Requirements

- RISC-V 64-bit architecture
- Vector extension (RVV) version 1.0
- Standard "gc" extensions (integer and compressed instructions)

## Implementation notes

- All routines are written in assembly in `dev/riscv64/src` and imported into `mlkem/src/native/riscv64/src` by `scripts/autogen` via `scripts/simpasm`. Compressed instructions and linker relaxation are disabled (`.option norvc`, `.option norelax`), so that the object code is fixed, as needed for formal verification.
- Multiplications by known constants (twiddles, scaling factors) use Barrett multiplication[^NeonNTT], based on `vsmul`. The routines set the fixed-point rounding mode `vxrm`, which is not preserved across calls.
- The register group sizes (LMUL) were chosen by benchmarks on the SpacemiT X60 (VLEN=256). `poly_reduce` and `poly_tomont` use LMUL=4, about twice as fast as LMUL=1. The base multiplication uses LMUL=2, about 20% faster than LMUL=1. Rejection sampling uses LMUL=2, about 25% faster than LMUL=1; LMUL=4 is slower again because of the cost of `vrgather` and `vcompress` on large register groups. Other microarchitectures may favor different choices.

<!--- bibliography --->
[^NeonNTT]: Becker, Hwang, Kannwischer, Yang, Yang: Neon NTT: Faster Dilithium, Kyber, and Saber on Cortex-A72 and Apple M1, [https://eprint.iacr.org/2021/986](https://eprint.iacr.org/2021/986)
