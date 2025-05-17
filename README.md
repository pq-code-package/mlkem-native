[//]: # (SPDX-License-Identifier: CC-BY-4.0)

# mlkem-native

![Base tests](https://github.com/pq-code-package/mlkem-native/actions/workflows/base.yml/badge.svg)
![Extended tests](https://github.com/pq-code-package/mlkem-native/actions/workflows/ci.yml/badge.svg)
![Proof: CBMC](https://github.com/pq-code-package/mlkem-native/actions/workflows/cbmc.yml/badge.svg)
![Proof: HOL-Light](https://github.com/pq-code-package/mlkem-native/actions/workflows/hol_light.yml/badge.svg)
![Benchmarks](https://github.com/pq-code-package/mlkem-native/actions/workflows/bench.yml/badge.svg)
![C90](https://img.shields.io/badge/language-C90-blue.svg)

[![License: Apache](https://img.shields.io/badge/license-Apache--2.0-green.svg)](https://www.apache.org/licenses/LICENSE-2.0)
[![License: ISC](https://img.shields.io/badge/License-ISC-blue.svg)](https://opensource.org/licenses/ISC)
[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](https://opensource.org/licenses/MIT)

mlkem-native is a secure, fast, and portable C90 implementation of ML-KEM[^FIPS203].
It is a fork of the ML-KEM reference implementation[^REF].

All C code in [mlkem/*](mlkem) and [mlkem/fips202/*](mlkem/fips202) is proved memory-safe (no memory overflow) and type-safe (no integer overflow)
using [CBMC](https://github.com/diffblue/cbmc). All AArch64 assembly is proved functionally correct at the object code level using
[HOL-Light](https://github.com/jrh13/hol-light).

mlkem-native includes fast assembly for AArch64 and AVX2, offering competitive performance on most Arm, Intel, and AMD platforms
(see [benchmarks](https://pq-code-package.github.io/mlkem-native/dev/bench/)).

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

## Applications

mlkem-native is used in [libOQS](https://github.com/open-quantum-safe/liboqs/) of the Open Quantum Safe project, and in AWS' Cryptography library [AWS-LC](https://github.com/aws/aws-lc/).

## Formal Verification

All C code in [mlkem/*](mlkem) and [mlkem/fips202/*](mlkem/fips202) is proved memory-safe (no memory overflow) and type-safe (no integer overflow).
This uses the [C Bounded Model Checker (CBMC)](https://github.com/diffblue/cbmc) and builds on function contracts and loop invariant annotations
in the source code. See [proofs/cbmc](proofs/cbmc) for details.

All AArch64 assembly is proved functionally correct at the object-code level. This uses the [HOL-Light](https://github.com/jrh13/hol-light)
interactive theorem prover and the [s2n-bignum](https://github.com/awslabs/s2n-bignum/) verification infrastructure (which includes a model of the
relevant parts of the Arm architecture). See [proofs/hol_light/arm](proofs/hol_light/arm) for details.

## Security

All assembly in mlkem-native is constant-time in the sense that it is free of secret-dependent control flow, memory access,
and instructions that are commonly variable-time, thwarting most timing side channels. C code is hardened against compiler-introduced
timing side channels (such as KyberSlash[^KyberSlash] or clangover[^clangover])
through suitable barriers and constant-time patterns.

Absence of secret-dependent branches, memory-access patterns and variable-latency instructions is also tested using `valgrind`
with various combinations of compilers and compilation options.

## State

mlkem-native is in beta-release stage. We believe it is ready for use, and hope to spark experiments on
integration into other software before issuing a stable release. If you have any feedback, please reach out! See
[RELEASE.md](RELEASE.md) for details.

## Design

mlkem-native is split into a _frontend_ and two _backends_ for arithmetic and FIPS202 / SHA3. The frontend is
fixed, written in C, and covers all routines that are not critical to performance. The backends are flexible, take care of
performance-sensitive routines, and can be implemented in C or native code (assembly/intrinsics); see
[mlkem/native/api.h](mlkem/native/api.h) for the arithmetic backend and
[mlkem/fips202/native/api.h](mlkem/fips202/native/api.h) for the FIPS-202 backend. mlkem-native currently
offers three backends for C, AArch64, and x86_64 - if you'd like contribute new backends, please reach out or just open a
PR.

Our AArch64 assembly is developed using the [SLOTHY](https://github.com/slothy-optimizer/slothy) superoptimizer, following the approach described in the SLOTHY paper[^SLOTHY_Paper]:
We write 'clean' assembly by hand and automate micro-optimizations (e.g. see the [clean](dev/aarch64_clean/src/ntt.S) vs [optimized](dev/aarch64_opt/src/ntt.S) AArch64 NTT).
See [dev/README.md](dev/README.md) for more details.

## Usage

mlkem-native is intended as a code package: If you want to use mlkem-native, import [mlkem/*](mlkem) into your
project's source tree and build using your favourite build system. See [examples/mlkem_native_as_code_package](examples/mlkem_native_as_code_package)
for an example. The build system provided in this repository is for development purposes only.

### Can I bring my own FIPS-202?

mlkem-native relies on and comes with an implementation of FIPS202[^FIPS202]. If your library has its own FIPS-202 implementation, you
can use it instead of the one shipped with mlkem-native: Replace
[`mlkem/fips202/*`](mlkem/fips202) by your FIPS-202 implementation, and make sure to include replacements for the headers
[`mlkem/fips202/fips202.h`](mlkem/fips202/fips202.h) and [`mlkem/fips202/fips202x4.h`](mlkem/fips202/fips202x4.h) and the functionalities specified
therein. See [FIPS202.md](FIPS202.md) for details, and
[examples/bring_your_own_fips202](examples/bring_your_own_fips202) for an example using
tiny_sha3[^tiny_sha3].

### Do I need to use the assembly backends?

No. If you want a C-only build, just omit the directories [mlkem/native](mlkem/native) and/or [mlkem/fips202/native](mlkem/fips202/native) from your import
and unset `MLK_CONFIG_USE_NATIVE_BACKEND_ARITH` and/or `MLK_CONFIG_USE_NATIVE_BACKEND_FIPS202` in your [config.h](mlkem/config.h).

### Do I need to setup CBMC to use mlkem-native?

No. While we recommend that you consider using it, mlkem-native will build + run fine without CBMC -- just make sure to
include [cbmc.h](mlkem/cbmc.h) and have `CBMC` undefined. In particular, you do _not_ need to remove all function
contracts and loop invariants from the code; they will be ignored unless `CBMC` is set.

### Does mlkem-native support all security levels of ML-KEM?

Yes. The security level is a compile-time parameter configured by setting `MLK_CONFIG_PARAMETER_SET=512/768/1024` in [config.h](mlkem/config.h).
If your library/application requires multiple security levels, you can build + link three instances of mlkem-native
while sharing common code; this is called a 'multi-level build' and is demonstrated in [examples/multilevel_build](examples/multilevel_build).

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

<!--- bibliography --->
[^FIPS202]: National Institute of Standards and Technology: FIPS202 SHA-3 Standard: Permutation-Based Hash and Extendable-Output Functions, [https://csrc.nist.gov/pubs/fips/202/final](https://csrc.nist.gov/pubs/fips/202/final)
[^FIPS203]: National Institute of Standards and Technology: FIPS 203 Module-Lattice-Based Key-Encapsulation Mechanism Standard, [https://csrc.nist.gov/pubs/fips/203/final](https://csrc.nist.gov/pubs/fips/203/final)
[^HYBRID]: Becker, Kannwischer: Hybrid scalar/vector implementations of Keccak and SPHINCS+ on AArch64, [https://eprint.iacr.org/2022/1243](https://eprint.iacr.org/2022/1243)
[^KyberSlash]: Bernstein, Bhargavan, Bhasin, Chattopadhyay, Chia, Kannwischer, Kiefer, Paiva, Ravi, Tamvada: KyberSlash: Exploiting secret-dependent division timings in Kyber implementations, [https://kyberslash.cr.yp.to/papers.html](https://kyberslash.cr.yp.to/papers.html)
[^REF]: Bos, Ducas, Kiltz, Lepoint, Lyubashevsky, Schanck, Schwabe, Seiler, Stehlé: CRYSTALS-Kyber C reference implementation, [https://github.com/pq-crystals/kyber/tree/main/ref](https://github.com/pq-crystals/kyber/tree/main/ref)
[^SLOTHY_Paper]: Abdulrahman, Becker, Kannwischer, Klein: Fast and Clean: Auditable high-performance assembly via constraint solving, [https://eprint.iacr.org/2022/1303](https://eprint.iacr.org/2022/1303)
[^clangover]: Antoon Purnal: clangover, [https://github.com/antoonpurnal/clangover](https://github.com/antoonpurnal/clangover)
[^tiny_sha3]: Markku-Juhani O. Saarinen: tiny_sha3, [https://github.com/mjosaarinen/tiny_sha3](https://github.com/mjosaarinen/tiny_sha3)
