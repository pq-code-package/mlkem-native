[//]: # (SPDX-License-Identifier: CC-BY-4.0)

mlkem-native v2.0.0
===================

Release notes
-------------

mlkem-native v2.0.0 is the second major release of mlkem-native. It follows
mlkem-native v1.3 and makes minor API changes: It removes the SUPERCOP `crypto_kem_*`
aliases and the legacy `MLK_CONFIG_API_*` path, splits the ambiguous `MLK_ERR_FAIL`
return code into specific error codes, and renames the FIPS-202 backend and
system-capability macros.

See the full change log here:
https://github.com/pq-code-package/mlkem-native/compare/v1.3.0...v2.0.0

Long-Term Support
-----------------

[`release/v1.3`](https://github.com/pq-code-package/mlkem-native/tree/release/v1.3) will
act as a support branch until February 2027 (inclusive). It will receive bugfixes, but no
new features. We do currently not plan to offer long-term support for mlkem-native v1.x beyond that timeframe.

If you are deploying mlkem-native v1.3 and expect to be unable to upgrade to
mlkem-native v2 by February 2027, please contact us to discuss a potential extension
of the support schedule.

Breaking changes since v1.3.0
-----------------------------

- Split the ambiguous `MLK_ERR_FAIL` return code into `MLK_ERR_INVALID_PK`
  (`-4`), `MLK_ERR_INVALID_SK` (`-5`), and `MLK_ERR_PCT_FAIL` (`-6`), returned
  respectively for a public key rejected by the FIPS 203 modulus check, a secret
  key rejected by the hash check, and a failed keygen pairwise consistency test.
  The codes `-1`..`-3` are unchanged; `MLK_ERR_FAIL` remains defined but is no
  longer returned by any function. Integrators mapping return codes into their
  own error space must handle the new values.
  ([#1852](https://github.com/pq-code-package/mlkem-native/pull/1852))
- Remove the SUPERCOP `crypto_kem_*` API aliases, the `MLK_CONFIG_NO_SUPERCOP`
  option, and the `CRYPTO_{PUBLICKEY,SECRETKEY,CIPHERTEXT}BYTES`,
  `CRYPTO_SYMBYTES` and `CRYPTO_BYTES` size constants. Consumers must use the
  namespaced API (e.g. `mlkem_keypair`) and derive sizes from
  `MLK_CONFIG_PARAMETER_SET`.
  ([#1857](https://github.com/pq-code-package/mlkem-native/pull/1857))
- Remove the legacy `MLK_CONFIG_API_*` configuration path. Configure builds
  through the configuration file instead, renaming `MLK_CONFIG_API_PARAMETER_SET`
  to `MLK_CONFIG_PARAMETER_SET`, `MLK_CONFIG_API_NAMESPACE_PREFIX` to
  `MLK_CONFIG_NAMESPACE_PREFIX`, `MLK_CONFIG_API_CONSTANTS_ONLY` to
  `MLK_CONFIG_CONSTANTS_ONLY`, and `MLK_CONFIG_API_QUALIFIER` to
  `MLK_CONFIG_EXTERNAL_API_QUALIFIER`. For a multi-level build, set
  `MLK_CONFIG_MULTILEVEL_BUILD`; the parameter set is now appended to the
  namespace prefix automatically.
  ([#1853](https://github.com/pq-code-package/mlkem-native/pull/1853))
- Prefix the `mlk_sys_cap` enum values with their architecture:
  `MLK_SYS_CAP_{AVX2,NEON,SHA3,MVE}` become
  `MLK_SYS_CAP_{X86_64_AVX2,AARCH64_NEON,AARCH64_SHA3,ARMV81M_MVE}`. Custom
  capability functions must use the new names.
  ([#1770](https://github.com/pq-code-package/mlkem-native/pull/1770))
- Rename the FIPS-202 backend function-support flags to the
  `MLK_USE_NATIVE_<function>` convention used by the arithmetic backend:
  `MLK_USE_FIPS202_X1_NATIVE` to `MLK_USE_NATIVE_FIPS202_X1`,
  `MLK_USE_FIPS202_X4_NATIVE` to `MLK_USE_NATIVE_FIPS202_X4`,
  `MLK_USE_FIPS202_X4_XOR_BYTES_NATIVE` to `MLK_USE_NATIVE_FIPS202_X4_XOR_BYTES`,
  and `MLK_USE_FIPS202_X4_EXTRACT_BYTES_NATIVE` to
  `MLK_USE_NATIVE_FIPS202_X4_EXTRACT_BYTES`. Custom FIPS-202 backends must rename
  these flags accordingly.
  ([#1775](https://github.com/pq-code-package/mlkem-native/pull/1775))

What's New
----------

### Assurance

- Axiomatize the default `mlk_zeroize` in CBMC via a contract for its
  zeroed-output postcondition, and configure the proofs with a failing custom
  `mlk_zeroize` so they must rely on the contract rather than the concrete
  implementation.
  ([#1850](https://github.com/pq-code-package/mlkem-native/pull/1850))
- Strengthen the top-level API contracts to check that output buffers are
  zeroized or left unmodified on error.
  ([#1850](https://github.com/pq-code-package/mlkem-native/pull/1850))

### Configuration / API

- Add the error codes `MLK_ERR_INVALID_PK`, `MLK_ERR_INVALID_SK`, and
  `MLK_ERR_PCT_FAIL`, distinguishing a rejected public key, a rejected secret
  key, and a failed keygen self-test. `mlk_check_pct` maps a key-check rejection
  of the freshly generated key to `MLK_ERR_PCT_FAIL` and passes platform
  failures through unmodified.
  ([#1852](https://github.com/pq-code-package/mlkem-native/pull/1852))

### Testing

- Support the FIPS 203-tr1 encapDecap revision in the ACVP client, accepting a
  decapsulation key supplied either as an expanded `dk` or as a `seed` (`d||z`)
  to expand, with `keyFormat` inspected per group. mlkem-native now supports and
  is tested against ACVP v1.1.0.43 in addition to the preceding two versions.
  ([#1811](https://github.com/pq-code-package/mlkem-native/pull/1811))
- Use runtime checks in the Wycheproof client instead of `assert`, which is
  stripped under `python -O` and could report a mismatching vector as passing.
  ([#1840](https://github.com/pq-code-package/mlkem-native/pull/1840))

### Documentation

- Add `API-CONVENTIONS.md` describing the conventions shared by all public
  functions: return values and the meaning of the `MLK_ERR_XXX` codes, pointer
  validity, and the state of output buffers on error. Link it from `README.md`
  and the `mlkem_native.h` preamble.
  ([#1843](https://github.com/pq-code-package/mlkem-native/pull/1843))
- Document the `MLK_ERR_RNG_FAIL` error returned by keygen.
  ([#1851](https://github.com/pq-code-package/mlkem-native/pull/1851))
- Clarify the scope and customization of `mlk_zeroize`.
  ([#1855](https://github.com/pq-code-package/mlkem-native/pull/1855))

mlkem-native v1.3.0
===================

Release notes
-------------

mlkem-native v1.3.0 adds configuration options to control which KEM operations
are included in a build. It also improves AArch64 feature detection and runtime
dispatch, and introduces ABI compliance checks for assembly backends. Embedded
testing now uses Zephyr across a broader range of Arm targets, while assembly
namespacing and source naming improve integration with projects such as AWS-LC.

See the full change log here:
https://github.com/pq-code-package/mlkem-native/compare/v1.2.0...v1.3.0

What's next? mlkem-native v2
----------------------------

This is expected to be the last release prior to mlkem-native v2. Between
v1.3.0 and v2, breaking changes to the `main` branch will be made.

Long-Term Support
-----------------

`release/v1.3` will act as a support branch until 6 months after
mlkem-native v2 is established. It will receive bugfixes, but no new features.
We do currently not plan to offer long-term support for mlkem-native v1.x
beyond that timeframe.

If you are deploying mlkem-native v1.3 and expect to be unable to upgrade to
mlkem-native v2 within 6 months of its release, please contact us to discuss
a potential extension of the support schedule.

What's New
----------

### Configuration / API

- Add `MLK_CONFIG_NO_KEYPAIR_API`, `MLK_CONFIG_NO_ENCAPS_API`, and
  `MLK_CONFIG_NO_DECAPS_API`, allowing unused KEM operations and their internal
  dependencies to be excluded. All non-empty API combinations are covered in
  CI. ([#1787](https://github.com/pq-code-package/mlkem-native/pull/1787))
- Gate the AArch64 arithmetic and FIPS-202 backends on compile-time NEON
  availability and the new `MLK_SYS_CAP_NEON` runtime capability. Integrators
  can now fall back to portable C on AArch64 systems without usable NEON.
  ([#1805](https://github.com/pq-code-package/mlkem-native/pull/1805),
  [#1809](https://github.com/pq-code-package/mlkem-native/pull/1809))
- Add `MLK_SYS_AARCH64_FAST_SHA3` to select the pure-Neon Armv8.4-A SHA3
  implementation on CPUs with sufficient SHA3 execution capacity, including
  Graviton5. ([#1784](https://github.com/pq-code-package/mlkem-native/pull/1784))

### Assurance / Testing

- Fix deterministic-only builds using `MLK_CONFIG_NO_RANDOMIZED_API`, including
  test, example, and stack-measurement coverage.
  ([#1816](https://github.com/pq-code-package/mlkem-native/pull/1816))
- Upgrade CBMC to v6.10.0, the newest release of CBMC including the fix
  [cbmc/#9011](https://github.com/diffblue/cbmc/pull/9011) to the Z3 soundness
  issue [z3/#9550](https://github.com/Z3Prover/z3/issues/9550). mlkem-native v1.2
  had pinned CBMC to an unstable version between v6.9 and v6.10 which already
  included that fix.
  ([#1762](https://github.com/pq-code-package/mlkem-native/pull/1762))
- Add assembly ABI checkers for AArch64, x86_64 SysV, ppc64le ELFv2, and
  Armv8.1-M MVE. The checkers verify preservation of callee-saved registers and
  run as part of the standard test suite.
  ([#1135](https://github.com/pq-code-package/mlkem-native/pull/1135))
- Add Zephyr-based testing for QEMU Cortex-M3, M4, M7, M33, and M55 targets,
  replacing the previous custom MPS baremetal platforms. Add test and benchmark
  support for the NUCLEO-N657X0-Q board.
  ([#1750](https://github.com/pq-code-package/mlkem-native/pull/1750),
  [#1547](https://github.com/pq-code-package/mlkem-native/pull/1547))
- Strengthen HOL Light tooling with cross-architecture proof execution and
  checks that every expected theorem is present
  ([#1634](https://github.com/pq-code-package/mlkem-native/pull/1634))
- Strengthen Wycheproof validation by checking newly specified fields, rejecting
  unknown schema fields, and tracking upstream vector changes.
  ([#1801](https://github.com/pq-code-package/mlkem-native/pull/1801))
- Extend Windows MSVC coverage to allocation-failure, RNG-failure, and
  Wycheproof tests ([#1738](https://github.com/pq-code-package/mlkem-native/pull/1738))
- Add emulated testing on x86_64 without AVX2.
  ([#1753](https://github.com/pq-code-package/mlkem-native/pull/1753))
- Correct decapsulation stack measurements, which previously returned before
  the full operation and understated peak stack use by around 10%.
  ([#1823](https://github.com/pq-code-package/mlkem-native/pull/1823))

### Integration / Upgrade Notes

- Namespace assembly-local labels with an `mlk_` prefix, preventing collisions
  when mlkem-native and other projects are combined into one assembly unit.
  ([#1813](https://github.com/pq-code-package/mlkem-native/pull/1813))
- Rename backend assembly files to be self-identifying. Arithmetic assembly
  filenames now use an `mlkem_` prefix. Downstream build systems with explicit
  source lists must update those paths.
  ([#1821](https://github.com/pq-code-package/mlkem-native/pull/1821))
- Move context-parameter support into the new `mlkem/src/context.h`; downstream
  source manifests must include this file.
  ([#1768](https://github.com/pq-code-package/mlkem-native/pull/1768))

mlkem-native v1.2.0
===================

Release notes
-------------

mlkem-native v1.2.0 adds a new **PowerPC (ppc64le)** assembly backend and broadens portability of the existing
backends: the x86_64 backend can now be used on Windows, the RISC-V backend compiles under C90, and a new
Cortex-M33 baremetal target is tested. It also fixes a signed-shift undefined behavior on 16-bit-`int` targets
and hardens the RISC-V backend against secret-dependent timing. Finally, the CBMC proofs are extended to
establish loop termination for all functions except rejection sampling.

What's New
----------

- **PowerPC (ppc64le) backend**: New VSX arithmetic backend (NTT, inverse NTT, `poly_reduce`, `poly_tomont`) for POWER8 and above, with automatic fallback to C on older targets. Thanks to IBM, and in particular Danny Tsen (@dannytsen) and Basil Hess (@bhess), for this contribution! ([#1677](https://github.com/pq-code-package/mlkem-native/pull/1677))
- **Assurance**: CBMC now proves loop termination for all functions except rejection sampling. Thanks to Nicky Mouha (@nmouha) for making us aware of the absence of termination proofs. ([#1625](https://github.com/pq-code-package/mlkem-native/pull/1625))
- **Verification tooling**: Bump CBMC to a development build that works around a Z3 soundness issue ([Z3#9550](https://github.com/Z3Prover/z3/issues/9550)) affecting the SMT solver used by the CBMC proofs. ([#1745](https://github.com/pq-code-package/mlkem-native/pull/1745))
- **Portability**: the x86_64 assembly backend can now be used on Windows with compilers that support the SysV calling convention per function (GCC and Clang, via `__attribute__((sysv_abi))`) ([#1730](https://github.com/pq-code-package/mlkem-native/pull/1730)), the RISC-V backend compiles under C90 ([#1732](https://github.com/pq-code-package/mlkem-native/pull/1732)), and a new Cortex-M33 baremetal target is tested ([#1579](https://github.com/pq-code-package/mlkem-native/pull/1579)).
- **Correctness / CT**: Fix signed-shift undefined behavior on 16-bit-`int` targets ([#1727](https://github.com/pq-code-package/mlkem-native/pull/1727)) and harden the RISC-V backend against secret-dependent timing ([#1732](https://github.com/pq-code-package/mlkem-native/pull/1732)).

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
