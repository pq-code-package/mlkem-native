[//]: # (SPDX-License-Identifier: CC-BY-4.0)

# mlkem-native

![Base tests](https://github.com/pq-code-package/mlkem-native/actions/workflows/base.yml/badge.svg)
![Extended tests](https://github.com/pq-code-package/mlkem-native/actions/workflows/ci.yml/badge.svg)
![Proof: CBMC](https://github.com/pq-code-package/mlkem-native/actions/workflows/cbmc.yml/badge.svg)
![Proof: HOL-Light](https://github.com/pq-code-package/mlkem-native/actions/workflows/hol_light.yml/badge.svg)
![Benchmarks](https://github.com/pq-code-package/mlkem-native/actions/workflows/bench.yml/badge.svg)
![C90](https://img.shields.io/badge/language-C90-blue.svg)
[![Apache](https://img.shields.io/badge/license-Apache--2.0-green.svg)](https://www.apache.org/licenses/LICENSE-2.0)

mlkem-native is a secure, fast, and portable C90 implementation of [ML-KEM](https://doi.org/10.6028/NIST.FIPS.203).
It is a fork of the ML-KEM [reference implementation](https://github.com/pq-crystals/kyber/tree/main/ref).

mlkem-native includes native backends for AArch64 and AVX2, offering competitive performance on most Arm, Intel, and AMD platforms
(see [benchmarks](https://pq-code-package.github.io/mlkem-native/dev/bench/)). The frontend and the C backend (i.e., all C code in [mlkem/*](mlkem) and [mlkem/fips202/*](mlkem/fips202)) are verified
using [CBMC](https://github.com/diffblue/cbmc) to be free of undefined behaviour. In particular, there are no out of
bounds accesses, nor integer overflows during optimized modular arithmetic.
[HOL-Light](https://github.com/jrh13/hol-light) is used to verify the functional correctness of core AArch64 assembly routines.

mlkem-native is supported by the [Post-Quantum Cryptography Alliance](https://pqca.org/) as part of the [Linux Foundation](https://linuxfoundation.org/).

## Quickstart for Ubuntu

```bash
# Install base packages
sudo apt-get update
sudo apt-get install make gcc python3 git

# Clone mlkem-native
git clone https://github.com/pq-code-package/mlkem-native.git
cd mlkem-native

# Build and run tests
make build
make test

# The same using `tests`, a convenience wrapper around `make`
./scripts/tests all
# Show all options
./scripts/tests --help
```

See [BUILDING.md](BUILDING.md) for more information.

## Security

mlkem-native is being developed with security at the top of mind. All native code is constant-time in the sense that
it is free of secret-dependent control flow, memory access, and instructions that are commonly variable-time,
thwarting most timing side channels.
The C code is hardened against compiler-introduced timing side channels (such as
[KyberSlash](https://kyberslash.cr.yp.to/) or [clangover](https://github.com/antoonpurnal/clangover))
through suitable barriers and constant-time patterns.
Absence of secret-dependent branches, memory-access patterns
and variable-latency instructions is also tested using `valgrind` with various combinations of compilers and
compilation options.

## Formal Verification

We use the [C Bounded Model Checker (CBMC)](https://github.com/diffblue/cbmc) to prove absence of various classes of
undefined behaviour in C, including out of bounds memory accesses and integer overflows. The proofs cover
all C code in [mlkem/*](mlkem) and [mlkem/fips202/*](mlkem/fips202) involved in running mlkem-native with its C backend.
See [proofs/cbmc](proofs/cbmc) for details.

The functional correctness of various AArch64 assembly routines is established using [HOL-Light](https://github.com/jrh13/hol-light) and the [s2n-bignum](https://github.com/awslabs/s2n-bignum/) verification infrastructure. The proofs can be found in [proofs/hol_light/arm](proofs/hol_light/arm) and were largely contributed by John Harrison. So far, the following functions have been proven correct:
- ML-KEM Arithmetic:
  * AArch64 forward NTT: [mlkem_ntt.S](proofs/hol_light/arm/mlkem/mlkem_ntt.S)
  * AArch64 inverse NTT: [mlkem_intt.S](proofs/hol_light/arm/mlkem/mlkem_intt.S)
  * AArch64 conversion to Montgomery form: [mlkem_poly_tomont.S](proofs/hol_light/arm/mlkem/mlkem_poly_tomont.S)
  * AArch64 'multiplication cache' computation: [mlkem_poly_mulcache_compute.S](proofs/hol_light/arm/mlkem/mlkem_poly_mulcache_compute.S)
- FIPS202:
  * Keccak-F1600 using lazy rotations (see [this paper](https://eprint.iacr.org/2022/1243)): [keccak_f1600_x1_scalar.S](proofs/hol_light/arm/mlkem/keccak_f1600_x1_scalar.S)
  * Keccak-F1600 using v8.4-A SHA3 instructions: [keccak_f1600_x1_v84a.S](proofs/hol_light/arm/mlkem/keccak_f1600_x1_v84a.S)
  * 2-fold Keccak-F1600 using v8.4-A SHA3 instructions: [keccak_f1600_x2_v84a.S](proofs/hol_light/arm/mlkem/keccak_f1600_x2_v84a.S)
  * 'Hybrid' 4-fold Keccak-F1600 using scalar and v8-A Neon instructions: [keccak_f1600_x4_v8a_scalar.S](proofs/hol_light/arm/mlkem/keccak_f1600_x4_v8a_scalar.S)
  * 'Triple hybrid' 4-fold Keccak-F1600 using scalar, v8-A Neon and v8.4-A+SHA3 Neon instructions: [keccak_f1600_x4_v8a_v84a_scalar.S](proofs/hol_light/arm/mlkem/keccak_f1600_x4_v8a_v84a_scalar.S)

## State

mlkem-native is in beta-release stage. We believe it is ready for use, and hope to spark experiments on
integration into other software before issuing a stable release. If you have any feedback, please reach out! See
[RELEASE.md](RELEASE.md) for details.

## Design

mlkem-native is split into a _frontend_ and two _backends_ for arithmetic and FIPS-202 (SHA3). The frontend is
fixed, written in C, and covers all routines that are not critical to performance. The backends are flexible, take care of
performance-sensitive routines, and can be implemented in C or native code (assembly/intrinsics); see
[mlkem/native/api.h](mlkem/native/api.h) for the arithmetic backend and
[mlkem/fips202/native/api.h](mlkem/fips202/native/api.h) for the FIPS-202 backend. mlkem-native currently
offers three backends for C, AArch64, and x86_64 - if you'd like contribute new backends, please reach out or just open a
PR.

Our AArch64 assembly is developed using [SLOTHY](https://github.com/slothy-optimizer/slothy): We write
'clean' assembly by hand and automate micro-optimizations (e.g. see the [clean](dev/aarch64_clean/src/ntt.S)
vs [optimized](dev/aarch64_opt/src/ntt.S) AArch64 NTT). See [dev/README.md](dev/README.md) for more details.

## Usage

mlkem-native is intended as a code package: If you want to use mlkem-native, import [mlkem/*](mlkem) into your
project's source tree and build using your favourite build system. See [examples/mlkem_native_as_code_package](examples/mlkem_native_as_code_package)
for an example. The build system provided in this repository is for development purposes only.

### Can I bring my own FIPS-202?

If your library has its own FIPS-202 implementation, you can use it instead of the one shipped with mlkem-native: Replace
[`mlkem/fips202/*`](mlkem/fips202) by your FIPS-202 implementation, and make sure to include replacements for the headers
[`mlkem/fips202/fips202.h`](mlkem/fips202/fips202.h) and [`mlkem/fips202/fips202x4.h`](mlkem/fips202/fips202x4.h) and the functionalities specified
therein. See [FIPS202.md](FIPS202.md) for details, and
[examples/bring_your_own_fips202](examples/bring_your_own_fips202) for an example using
[tiny_sha3](https://github.com/mjosaarinen/tiny_sha3/).

### Do I need to use the assembly backends?

No. If you want a C-only build, just omit the directories [mlkem/native](mlkem/native) and/or [mlkem/fips202/native](mlkem/fips202/native) from your import
and unset `MLK_USE_NATIVE_BACKEND_ARITH` and/or `MLK_USE_NATIVE_BACKEND_FIPS202` in your [config.h](mlkem/config.h).

### Do I need to setup CBMC to use mlkem-native?

No. While we recommend that you consider using it, mlkem-native will build + run fine without CBMC -- just make sure to
include [cbmc.h](mlkem/cbmc.h) and have `CBMC` undefined. In particular, you do _not_ need to remove all function
contracts and loop invariants from the code; they will be ignored unless `CBMC` is set.

### Does mlkem-native support all security levels of ML-KEM?

Yes. The security level is a compile-time parameter configured by setting `MLKEM_K=2/3/4` in [config.h](mlkem/config.h).
If your library/application requires multiple security levels, you can build + link three instances of mlkem-native
while sharing common code; this is called a 'multilevel build' and is demonstrated in [examples/multilevel_build](examples/multilevel_build).

### Can I bring my own backend?

Yes, you can add further backends for ML-KEM native arithmetic and/or for FIPS-202. Follow the existing backends
as templates or see [examples/custom_backend](examples/custom_backend) for a minimal example how to register a custom backend.

## Have a Question?

If you think you have found a security bug in mlkem-native, please report the vulnerability through
Github's [private vulnerability reporting](https://github.com/pq-code-package/mlkem-native/security). Please do **not**
create a public GitHub issue.

If you have any other question / non-security related issue / feature request, please open a GitHub issue.

## Contributing

If you want to help us build mlkem-native, please reach out. You can contact the mlkem-native team
through the [PQCA Discord](https://discord.com/invite/xyVnwzfg5R). See also [CONTRIBUTING.md](CONTRIBUTING.md).
