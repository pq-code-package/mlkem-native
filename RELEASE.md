[//]: # (SPDX-License-Identifier: CC-BY-4.0)

mlkem-native v2.1.0
===================

Release notes
-------------

mlkem-native v2.1.0 adds further backends, reduces RAM usage, and
strengthens the trust anchor for its verification artifacts.

See the [full change log](https://github.com/pq-code-package/mlkem-native/compare/v2.0.0...58721ebde4b682bb3384ef7d11333e4f0ddb0164)
and the [v2.0.0 release notes](https://github.com/pq-code-package/mlkem-native/blob/v2.0.0/RELEASE.md).

Backends
--------

- **x86_64.** A new FIPS 202 backend accelerates Keccak on AVX-512 targets.
  If a custom runtime check rejects AVX-512, the AVX-512 routines fall back
  to C. If you require a portable build applying AVX-512, AVX2 or C backend
  as applicable to the host, you currently need to write custom dispatch logic.
  ([#2018](https://github.com/pq-code-package/mlkem-native/pull/2018))

  The speedup varies by CPU. Across ML-KEM-1024 key generation, encapsulation,
  and decapsulation, EC2 benchmarks show about 11–16% fewer cycles on AMD c7a
  and 16–23% fewer on Intel c7i and c8i.
  ([Benchmarks](https://pq-code-package.github.io/mlkem-native/dev/bench/))

- **AArch64.** Neon implementations of polynomial compression,
  decompression, and decoding complete the arithmetic backend.
  ([#2000](https://github.com/pq-code-package/mlkem-native/pull/2000))

  For ML-KEM-1024 on Graviton3 and Graviton4 (EC2 c7g and c8g),
  encapsulation uses about 4% fewer cycles and decapsulation uses about 6% fewer.
  On a Cortex-A76 (Raspberry Pi 5), the reductions are about 3% and 6%.
  ([Benchmarks](https://pq-code-package.github.io/mlkem-native/dev/bench/))

RAM usage
---------

The AArch64 rejection sampler now writes coefficients directly to its
output buffer, removing its 576-byte stack allocation.
([#2025](https://github.com/pq-code-package/mlkem-native/pull/2025))

Trust
-----

With new proofs being primarily written by AI, the soundness of verification
is of increasing importance.

v2.1 introduces proof capture and replay using [HOLTrace](https://holtrace.cr.yp.to/)
to remove the need to review and trust HOL Light proof scripts. In particular, this
detects proof scripts that cheat by adding new axioms, bypassing the kernel, or using
non-standard definitions. See [hol_trace/README.md](proofs/hol_light/hol_trace/README.md)
and [SOUNDNESS.md](SOUNDNESS.md) for details.
([#1972](https://github.com/pq-code-package/mlkem-native/pull/1972))

Further, all 64-bit CBMC proof harnesses are now checked against at least two solvers.
This reduces reliance on any single solver and thereby reduces the likelihood of
soundness issues. ([#1959](https://github.com/pq-code-package/mlkem-native/pull/1959))

Bug fixes
---------

- **AArch64 alignment.** Fixed alignment faults in the rejection sampler on
  targets that require aligned accesses.
  ([#2025](https://github.com/pq-code-package/mlkem-native/pull/2025))
- **Decapsulation.** Keep intermediate secret values out of the caller's
  output buffer.
  ([issue #1909](https://github.com/pq-code-package/mlkem-native/issues/1909),
  [#1995](https://github.com/pq-code-package/mlkem-native/pull/1995))
