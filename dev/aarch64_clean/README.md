[//]: # (SPDX-License-Identifier: CC-BY-4.0)

# AArch64 backend (little endian)

This directory contains a native backend for little endian AArch64 systems. It is derived from [^NeonNTT] [^SLOTHY_Paper].

## Variants

This backend comes in two versions: "clean" and optimized. This directory contains the "clean" backend which is handwritten and
meant to be easy to read and modify; for example, it heavily leverages register aliases and assembly macros. The optimized version
is automatically generated from the clean one via [SLOTHY](https://github.com/slothy-optimizer/slothy). Currently, the
target architecture is Neoverse N1, but you can easily re-optimize the code for a different microarchitecture supported
by SLOTHY, by adjusting the parameters in the [Makefile](../aarch64_opt/src/Makefile).

## Compression and serialization kernels

SLOTHY does not optimize the kernels for `poly_compress_d{4,5,10,11}`, `poly_decompress_d{4,5,10,11}` and
`poly_frombytes` yet: the [Makefile](../aarch64_opt/src/Makefile) copies them unchanged. Byte buffers can have any
alignment and are accessed only with `ld1`/`ld3`/`st1` on byte lanes. The `poly_decompress_d*` kernels and
`poly_compress_d5` take a table of constant vectors as their last argument; `scripts/autogen` generates it into
`<kernel>_table.c` and the HOL-Light definition `mlkem_<kernel>_table.ml` from a single source. Each kernel's header
comment describes its approach.

<!--- bibliography --->
[^NeonNTT]: Becker, Hwang, Kannwischer, Yang, Yang: Neon NTT: Faster Dilithium, Kyber, and Saber on Cortex-A72 and Apple M1, [https://eprint.iacr.org/2021/986](https://eprint.iacr.org/2021/986)
[^SLOTHY_Paper]: Abdulrahman, Becker, Kannwischer, Klein: Fast and Clean: Auditable high-performance assembly via constraint solving, [https://eprint.iacr.org/2022/1303](https://eprint.iacr.org/2022/1303)
