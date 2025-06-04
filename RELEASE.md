[//]: # (SPDX-License-Identifier: CC-BY-4.0)
mlkem-native v1.0.0
==================

Release notes
-------------

v1.0.0 is the first stable release of mlkem-native, a secure, fast and portable C90 implementation of [ML-KEM](https://csrc.nist.gov/pubs/fips/203/final) derived from the ML-KEM reference implementation. mlkem-native v1.0.0 offers:
* High maintainability and extensibility through modular frontend/backend design.
* High performance through Arch64 and AVX2 assembly backends and the use of the [SLOTHY super-optimizer](https://github.com/slothy-optimizer/slothy).
* High assurance through memory- and type-safety proofs for the C frontend + backend, functional correctness proofs for all AArch64 assembly, and extensive constant-time testing.

mlkem-native-v1.0.0 is uniformly licensed Apache-2.0 OR MIT OR ISC, giving consumers the choice to use any of these licenses.

What's New
----------

Compared to [v1.0.0-beta](https://github.com/pq-code-package/mlkem-native/releases/tag/v1.0.0-beta) the following
major improvements have been integrated into mlkem-native:

- Completion of functional correctness proofs of the AArch64 backend
- Uniform licensing of all code in mlkem/* under Apache-2.0 OR ISC OR MIT
- Numerous configuration option improvements
- Numerous documentation improvements

See the full change log here: https://github.com/pq-code-package/mlkem-native/compare/v1.0.0-beta...v1.0.0
