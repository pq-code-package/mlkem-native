[//]: # (SPDX-License-Identifier: CC-BY-4.0)

![mlkem_native_logo](docs/images/mlkem_native.png)

# mlkem-native

![CI](https://github.com/pq-code-package/mlkem-native/actions/workflows/ci.yml/badge.svg)
![Benchmarks](https://github.com/pq-code-package/mlkem-native/actions/workflows/bench.yml/badge.svg)
[![C90](https://img.shields.io/badge/language-C90-blue.svg)](https://web.archive.org/web/20200909074736if_/https://www.pdf-archive.com/2014/10/02/ansi-iso-9899-1990-1/ansi-iso-9899-1990-1.pdf)
[![Apache](https://img.shields.io/badge/license-Apache--2.0-green.svg)](https://www.apache.org/licenses/LICENSE-2.0)

mlkem-native is a C90 implementation of [ML-KEM](https://doi.org/10.6028/NIST.FIPS.203.ipd) targeting
PC, mobile and server platforms. It is a fork of the ML-KEM [reference
implementation](https://github.com/pq-crystals/kyber/tree/main/ref).

mlkem-native aims to be secure, fast, and easy to use: It provides native code backends in C, AArch64 and
x86_64, offering state of the art performance on most Arm, Intel and AMD platforms (see
[benchmarks](https://pq-code-package.github.io/mlkem-native/dev/bench/)). The C code in [mlkem/*](mlkem) is verified
using [CBMC](https://github.com/diffblue/cbmc) to be free of undefined behaviour. In particular, there are no out of
bounds accesses, nor integer overflows during optimized modular arithmetic.

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

## Formal Verification

We use the [C Bounded Model Checker (CBMC)](https://github.com/diffblue/cbmc) to prove absence of various classes of
undefined behaviour in C, including out of bounds memory accesses and integer overflows. At present, the proofs cover
all C code in [mlkem/*](mlkem) involved in running mlkem-native with its C backend. See [cbmc](cbmc) for
details.

Experiments are underway to verify assembly using the [HOL-Light](https://hol-light.github.io/) theorem prover
and the [s2n-bignum](https://github.com/awslabs/s2n-bignum) infrastructure (e.g. see
[here](https://github.com/jargh/s2n-bignum-dev/tree/mlkem) for proofs of SLOTHY-optimized versions of the AArch64 NTT
and invNTT by John Harrison).

## State

mlkem-native is in alpha-release stage. We believe it is ready for use, and hope to spark experiments on
integration into other software before issuing a stable release. If you have any feedback, please reach out! See
[RELEASE.md](RELEASE.md) for details.

## Design

mlkem-native is split in a _frontend_ and two _backends_ for arithmetic and FIPS-202 (SHA3). The frontend is
fixed, written in C and covers all routines that are not critical to performance. The backends are flexible, take care of
performance-sensitive routines, and can be implemented in C or native code (assembly/intrinsics); see
[mlkem/native/api.h](mlkem/native/api.h) for the arithmetic backend and
[mlkem/fips202/native/api.h](mlkem/fips202/native/api.h) for the FIPS-202 backend. mlkem-native currently
offers three backends for C, AArch64 and x86_64 - if you'd like contribute new backends, please reach out or just open a
PR.

Our AArch64 assembly is developed using [SLOTHY](https://github.com/slothy-optimizer/slothy): We write
'clean' assembly by hand and automate micro-optimizations (e.g. see the [clean](mlkem/native/aarch64/src/ntt_clean.S)
vs [optimized](mlkem/native/aarch64/src/ntt_opt.S) AArch64 NTT).

## How should I use mlkem-native?

mlkem-native is currently intended to be used as a code package, where source files are imported into a consuming
project's source tree and built using that project's build system. See
[examples/mlkem_native_as_code_package](examples/mlkem_native_as_code_package) for an example. The build system provided
in this repository is for experimental and development purposes only. If you prefer a library-build, please get in touch or open an issue.

### Can I bring my own backend?

Absolutely: You can add further backends for ML-KEM native arithmetic and/or for FIPS-202. Follow the existing backends
as templates, or see [examples/custom_backend](examples/custom_backend) for a minimal example how to register a custom backend.

### Can I bring my own FIPS-202?

If your library has a FIPS-202 implementation, you can use it instead of the one shipped with mlkem-native: Replace
[`mlkem/fips202/*`](mlkem/fips202) by your FIPS-202 implementation, and make sure to include replacements for the headers
[`mlkem/fips202/fips202.h`](mlkem/fips202/fips202.h) and [`mlkem/fips202/fips202x4.h`](mlkem/fips202/fips202x4.h) and the functionalities specified
therein. See [FIPS202.md](FIPS202.md) for details, and
[examples/bring_your_own_fips202](examples/bring_your_own_fips202) for an example using
[tiny_sha3](https://github.com/mjosaarinen/tiny_sha3/).

### Do I need to setup CBMC to use mlkem-native?

No. While we recommend that you consider using it, mlkem-native will build + run fine without CBMC -- just make sure to
include [cbmc.h](mlkem/cbmc.h) and have `CBMC` undefined. In particular, you do _not_ need to remove all function
contracts and loop invariants from the code; they will be ignored unless `CBMC` is set.

## Have a Question?

If you think you have found a security bug in mlkem-native, please report the vulnerability through
Github's [private vulnerability reporting](https://github.com/pq-code-package/mlkem-native/security). Please do **not**
create a public GitHub issue.

If you have any other question / non-security related issue / feature request, please open a GitHub issue.

## Contributing

If you want to help us build mlkem-native, please reach out. You can contact the mlkem-native team
through the [PQCA Discord](https://discord.com/invite/xyVnwzfg5R).
