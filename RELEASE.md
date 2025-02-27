[//]: # (SPDX-License-Identifier: CC-BY-4.0)
mlkem-native v1.0.0-beta
==================

About
-----

mlkem-native is a secure, fast and portable C90 implementation of [ML-KEM](https://doi.org/10.6028/NIST.FIPS.203).
It is a fork of the ML-KEM [reference implementation](https://github.com/pq-crystals/kyber/tree/main/ref).

mlkem-native includes native backends for AArch64 and AVX2, offering competitive performance on most Arm, Intel and AMD platforms
(see [benchmarks](https://pq-code-package.github.io/mlkem-native/dev/bench/)). The frontend and the C backend (i.e., all C code in [mlkem/*](mlkem) and [mlkem/fips202/*](mlkem/fips202)) are verified
using [CBMC](https://github.com/diffblue/cbmc) to be free of undefined behaviour. In particular, there are no out of
bounds accesses, nor integer overflows during optimized modular arithmetic.
HOL-Light is used to verify functional correctness of selected AArch64 assembly routines.

mlkem-native is supported by the [Post-Quantum Cryptography Alliance](https://pqca.org/) as part of the [Linux Foundation](https://linuxfoundation.org/).

Release notes
=============

This is the second official release of mlkem-native, a secure, fast and portable C90 implementation of [ML-KEM](https://doi.org/10.6028/NIST.FIPS.203).
This beta release expands the scope of formal verification (using CBMC and HOL-Light), improves FIPS compliance by adding improves FIPS compliance by adding PCT, buffer zeroization, and documentation, and increases the confidence in resistance against timing side-channels through extensive Valgrind-based testing.

What's New
----------

Compared to [v1.0.0-alpha](https://github.com/pq-code-package/mlkem-native/releases/tag/v1.0.0-alpha) the following
major improvements have been integrated into mlkem-native:
- Full CBMC proof coverage of the C frontend and backend including FIPS202
- Destruction of intermediate values in https://github.com/pq-code-package/mlkem-native/pull/763
- Functional correctness proofs for AArch64 NTT and INTT in https://github.com/pq-code-package/mlkem-native/pull/662
- Functional correctness proofs for Keccakx1 in https://github.com/pq-code-package/mlkem-native/pull/826 and https://github.com/pq-code-package/mlkem-native/pull/821
- Support for single compilation-unit builds in https://github.com/pq-code-package/mlkem-native/pull/612
- Addition of the pair-wise consistency test in https://github.com/pq-code-package/mlkem-native/pull/769
- Valgrind-based constant-time tests in https://github.com/pq-code-package/mlkem-native/pull/687
- Valgrind-based detection of secret-dependent variable-latency instruction in https://github.com/pq-code-package/mlkem-native/pull/693
- Improved x86_64 backend performance in https://github.com/pq-code-package/mlkem-native/pull/709
- Documentation of differences to the reference implementation in https://github.com/pq-code-package/mlkem-native/pull/799
- Addition of references to FIPS algorithms and equations to relevant functions in https://github.com/pq-code-package/mlkem-native/pull/776
- Numerous documentation improvements
- Additional examples on using mlkem-native (see [examples/](examples/))

See the full change log here: https://github.com/pq-code-package/mlkem-native/compare/v1.0.0-alpha...v1.0.0-beta
