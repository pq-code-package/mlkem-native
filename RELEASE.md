[//]: # (SPDX-License-Identifier: CC-BY-4.0)
mlkem-native alpha
==================

About
-----

mlkem-native is a C90 implementation of [ML-KEM](https://doi.org/10.6028/NIST.FIPS.203) targeting
PC, mobile and server platforms. It is a fork of the ML-KEM [reference
implementation](https://github.com/pq-crystals/kyber/tree/main/ref).

mlkem-native aims to be fast, secure, and easy to use: It provides native code backends in C, AArch64 and
x86_64, offering state-of-the-art performance on most Arm, Intel and AMD platforms. The C code in [mlkem/*](mlkem) is
verified using [CBMC](https://github.com/diffblue/cbmc) to be free of undefined behavior. In particular, there are no
out of bounds accesses, nor integer overflows during optimized modular arithmetic.

Release notes
=============

This is first official release of mlkem-native, a C90 implementation of [ML-KEM](https://doi.org/10.6028/NIST.FIPS.203) targeting
PC, mobile and server platforms.
This alpha release of mlkem-native features complete backends in C, AArch64 and x86_64, offering state-of-the-art performance on most Arm, Intel and AMD platforms.

With this alpha release we intend to spark experiments on integrations of mlkem-native in other software.
We appreciate any feedback on how to improve and extend mlkem-native in the future.
Please open an issue on https://github.com/pq-code-package/mlkem-native.
While we continue on improving and extending mlkem-native, we expect that the majority of the code is stable.
In particular, the core external APIs are stable; we will potentially expose additional functions (e.g., operating on expanded secret keys) in the future.
