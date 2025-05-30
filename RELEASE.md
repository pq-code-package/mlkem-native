[//]: # (SPDX-License-Identifier: CC-BY-4.0)
mlkem-native v1.0.0
==================

About
-----

mlkem-native is a secure, fast and portable C90 implementation of [ML-KEM](https://doi.org/10.6028/NIST.FIPS.203).
It is a fork of the ML-KEM [reference implementation](https://github.com/pq-crystals/kyber/tree/main/ref).

All C code in [mlkem/*](mlkem) and [mlkem/fips202/*](mlkem/fips202) is proved memory-safe (no memory overflow) and type-safe (no integer overflow)
using [CBMC](https://github.com/diffblue/cbmc). All AArch64 assembly is proved functionally correct at the object code level using
[HOL-Light](https://github.com/jrh13/hol-light).

mlkem-native includes fast assembly for AArch64 and AVX2, offering competitive performance on most Arm, Intel, and AMD platforms
(see [benchmarks](https://pq-code-package.github.io/mlkem-native/dev/bench/)).

mlkem-native is supported by the [Post-Quantum Cryptography Alliance](https://pqca.org/) as part of the [Linux Foundation](https://linuxfoundation.org/).

Release notes
=============

v1.0.0 is the first official stable release of mlkem-native, a secure, fast and portable C90 implementation of [ML-KEM](https://doi.org/10.6028/NIST.FIPS.203). It follows the previous alpha (v1.0.0-alpha) and beta (v1.0.0-beta) releases.

This first stable release marks the completion of the functional correctness proofs of the AArch64 backend.
It also now comes with uniform licensing under Apache-2.0 OR ISC OR MIT giving consumers the choice to use any of these licenses.

What's New
----------

Compared to [v1.0.0-beta](https://github.com/pq-code-package/mlkem-native/releases/tag/v1.0.0-beta) the following
major improvements have been integrated into mlkem-native:

- Completion of functional correctness proofs of the AArch64 backend
- Uniform licensing of all code in mlkem/* under Apache-2.0 OR ISC OR MIT
- Numerous configuration option improvements
- Numerous documentation improvements

See the full change log here: https://github.com/pq-code-package/mlkem-native/compare/v1.0.0-beta...v1.0.0
