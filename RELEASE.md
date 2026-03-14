[//]: # (SPDX-License-Identifier: CC-BY-4.0)
mlkem-native v1.1.0
====================

Release notes
-------------

mlkem-native v1.1.0 marks the completion of the verification of all x86_64 and AArch64 assembly and the introduction of
[SOUNDNESS.md](SOUNDNESS.md) documenting the scope, assumptions and risks of the verification work. It also introduces
various configuration options enabling the customization of mlkem-native for different application contexts. Finally,
new backends for RISC-V RVV and Armv8.1-M MVE have been added.

See the full change log here: https://github.com/pq-code-package/mlkem-native/compare/v1.0.0...v1.1.0

What's New
----------

### Security

- Fix missing zeroization of intermediate polynomial vector `pkpv` in `mlk_indcpa_keypair_derand()` and `mlk_indcpa_enc()`. ([#1328](https://github.com/pq-code-package/mlkem-native/pull/1328))
- Fix missing zeroization of `pk` and `sk` buffers on keypair generation failure (e.g. OOM during the pairwise consistency test). ([#1559](https://github.com/pq-code-package/mlkem-native/pull/1559))
- Fix a 4-byte buffer overread in x86_64 rejection sampling assembly. The overread was within the stack frame and the excess bytes were not acted on, but the read itself exceeded the nominal buffer bounds. Found while working on the corresponding memory-safety proof. ([#1615](https://github.com/pq-code-package/mlkem-native/pull/1615))
- Make the value barrier `volatile` to prevent compilers from optimizing it away, strengthening the constant-time countermeasure. This is a purely preventative measure; no insecure compilations of the previous value barrier have been noted. ([#1342](https://github.com/pq-code-package/mlkem-native/pull/1342))
- Mark the stack as non-executable in all assembly files via `.note.GNU-stack` section markers. ([#1340](https://github.com/pq-code-package/mlkem-native/pull/1340))

### Assurance

- **Assembly verification:** All x86_64 and AArch64 assembly is verified to be functionally correct, memory-safe and
  free of secret-dependent timing, in HOL Light.
- **SOUNDNESS.md**: New document mapping out what is proved, what is assumed, and where the gaps and risks
  lie. ([#1582](https://github.com/pq-code-package/mlkem-native/pull/1582))

### Performance

- **AArch64**: Re-optimized arithmetic backend for Neoverse-N1 using SLOTHY. ([#1088](https://github.com/pq-code-package/mlkem-native/pull/1088))
- **x86_64**: AVX2 assembly for `polyvec_basemul` ([#1097](https://github.com/pq-code-package/mlkem-native/pull/1097)), SSE4.1 rejection sampling ([#1136](https://github.com/pq-code-package/mlkem-native/pull/1136)), conversion of compression/decompression from intrinsics to assembly ([#1543](https://github.com/pq-code-package/mlkem-native/pull/1543), [#1545](https://github.com/pq-code-package/mlkem-native/pull/1545)), and replacement of the Keccak-f1600 x4 C intrinsics with formally verified AVX2 assembly from s2n-bignum ([#1576](https://github.com/pq-code-package/mlkem-native/pull/1576)).
- **RISC-V RVV**: Native backend for rv64gcv targets using the RISC-V Vector Extension 1.0, providing vectorized NTT,
  inverse NTT, polynomial arithmetic, and rejection sampling. NTT and invNTT are for VLEN >= 256, with automatic
  fallback to C for VLEN=128. Other functions are VLEN agnostic. ([#1037](https://github.com/pq-code-package/mlkem-native/pull/1037))
- **Armv8.1-M MVE**: Experimental native backend for Cortex-M55 and similar targets, including MVE Keccak-f1600 x4 and baremetal build support for the MPS3 AN547 platform. ([#1220](https://github.com/pq-code-package/mlkem-native/pull/1220), [#1518](https://github.com/pq-code-package/mlkem-native/pull/1518), [#1524](https://github.com/pq-code-package/mlkem-native/pull/1524))

### Configuration / API

- `MLK_CONFIG_CUSTOM_ALLOC_FREE`: Custom allocation/deallocation for large internal structures, for systems with limited stack space. ([#1389](https://github.com/pq-code-package/mlkem-native/pull/1389))
- `MLK_CONFIG_CONTEXT_PARAMETER`: Add opaque context parameter to top-level API, passed through to custom alloc/free
  routines enabled via `MLK_CONFIG_CUSTOM_ALLOC_FREE`. Useful for applications without global allocator context. ([#1467](https://github.com/pq-code-package/mlkem-native/pull/1467))
- `MLK_CONFIG_NO_RANDOMIZED_API`: Build only the deterministic (`_derand`) API. ([#1185](https://github.com/pq-code-package/mlkem-native/pull/1185))
- `MLK_CONFIG_SERIAL_FIPS202_ONLY`: Disable 4x-batched FIPS-202, allowing use of a simpler serial-only FIPS-202 backend. ([#1231](https://github.com/pq-code-package/mlkem-native/pull/1231))
- Runtime backend dispatch based on a custom CPU capabilities function. ([#1152](https://github.com/pq-code-package/mlkem-native/pull/1152))
- `randombytes()` may now return an error code, which is propagated through the KEM API. ([#1331](https://github.com/pq-code-package/mlkem-native/pull/1331))
- `mlk_kem_check_pk()` / `mlk_kem_check_sk()` added to the public API for FIPS 203 modulus and hash checks. ([#1216](https://github.com/pq-code-package/mlkem-native/pull/1216))
- C++ compatibility for `mlkem_native.h`. ([#1465](https://github.com/pq-code-package/mlkem-native/pull/1465))
- `MLK_CONFIG_CUSTOM_MEMCPY` / `MLK_CONFIG_CUSTOM_MEMSET`: Custom replacements for `memcpy` and `memset`. ([#1105](https://github.com/pq-code-package/mlkem-native/pull/1105))

### Testing

- Wycheproof test suite for ML-KEM test vector validation. ([#1588](https://github.com/pq-code-package/mlkem-native/pull/1588))
- Unit test framework for internal functions with native backend consistency checks. ([#1188](https://github.com/pq-code-package/mlkem-native/pull/1188))
- Allocation failure testing, RNG failure testing, stack usage measurement, and unaligned buffer testing.
- Baremetal testing on AVR (16-bit) and AArch64-virt (no MMU).

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
