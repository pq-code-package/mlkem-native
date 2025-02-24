[//]: # (SPDX-License-Identifier: CC-BY-4.0)

Relation to reference implementation
====================================

mlkem-native is a fork of the ML-KEM [reference implementation](https://github.com/pq-crystals/kyber).

The following gives an overview of the major changes:

- CBMC and debug annotations, and minor code restructurings or signature changes to facilitate the CBMC proofs. For example, `poly_add(x,a)` only comes in a destructive variant to avoid specifying aliasing constraints; `poly_rej_uniform` has an additional `offset` parameter indicating the position in the sampling buffer, to avoid passing shifted pointers).
- Introduction of 4x-batched versions of some functions from the reference implementation. This is to leverage 4x-batched Keccak-f1600 implementations if present. The batching happens at the C level even if no native backend for FIPS 202 is present.
- FIPS 203 compliance: Introduced PK (FIPS 203, Section 7.2, 'modulus check') and SK (FIPS 203, Section 7.3, 'hash check') check, as well as optional PCT (FIPS 203, Section 7.1, Pairwise Consistency). Also, introduced zeroization of stack buffers as required by (FIPS 203, Section 3.3, Destruction of intermediate values).
- Introduction of native backend implementations. With the exception of the native backend for `poly_rej_uniform()`, which may fail and fall back to the C implementation, those are drop-in replacements for the corresponding C functions and dispatched at compile-time.
- Restructuring of files to separate level-specific from level-generic functionality. This is needed to enable a multi-level build of mlkem-native where level-generic code is shared between levels.
- More pervasive use of value barriers to harden constant-time primitives, even when Link-Time-Optimization (LTO) is enabled. The use of LTO can lead to insecure compilation in case of the reference implementation.
- Use of a multiplication cache ('mulcache') structure to simplify and speedup the base multiplication.
- Different placement of modular reductions: We reduce to _unsigned_ canonical representatives in `poly_reduce()`, and _assume_ such in all polynomial compression functions. The reference implementation works with a _signed_ `poly_reduce()`, and embeds various signed->unsigned conversions in the compression functions.
- More inlining: Modular multiplication and primitives are in a header rather than a separate compilation unit.

For details, please see the source code: Functions in the mlkem-native source tree are annotated with `/* Reference: ... */` comments to outline how they relate to the reference implementation.
