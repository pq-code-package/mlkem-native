[//]: # (SPDX-License-Identifier: CC-BY-4.0)
[//]: # (This file is auto-generated from BIBLIOGRAPHY.yml)
[//]: # (Do not modify it directly)

# Bibliography

This file lists the citations made throughout the mlkem-native 
source code and documentation.

### `AVX2_NTT`

* Faster AVX2 optimized NTT multiplication for Ring-LWE lattice cryptography.
* Author(s):
  - Gregor Seiler
* URL: https://eprint.iacr.org/2018/039
* Referenced from:
  - [dev/x86_64/src/intt.S](dev/x86_64/src/intt.S)
  - [dev/x86_64/src/ntt.S](dev/x86_64/src/ntt.S)
  - [mlkem/src/native/x86_64/src/intt.S](mlkem/src/native/x86_64/src/intt.S)
  - [mlkem/src/native/x86_64/src/ntt.S](mlkem/src/native/x86_64/src/ntt.S)

### `FIPS140_3_IG`

* Implementation Guidance for FIPS 140-3 and the Cryptographic Module Validation Program
* Author(s):
  - National Institute of Standards and Technology
* URL: https://csrc.nist.gov/projects/cryptographic-module-validation-program/fips-140-3-ig-announcements
* Referenced from:
  - [integration/liboqs/config_aarch64.h](integration/liboqs/config_aarch64.h)
  - [integration/liboqs/config_c.h](integration/liboqs/config_c.h)
  - [integration/liboqs/config_ppc64le.h](integration/liboqs/config_ppc64le.h)
  - [integration/liboqs/config_x86_64.h](integration/liboqs/config_x86_64.h)
  - [mlkem/src/config.h](mlkem/src/config.h)
  - [mlkem/src/kem.c](mlkem/src/kem.c)
  - [test/break_pct_config.h](test/break_pct_config.h)
  - [test/custom_memcpy_config.h](test/custom_memcpy_config.h)
  - [test/custom_memset_config.h](test/custom_memset_config.h)
  - [test/custom_native_capability_config_0.h](test/custom_native_capability_config_0.h)
  - [test/custom_native_capability_config_1.h](test/custom_native_capability_config_1.h)
  - [test/custom_native_capability_config_CPUID_AVX2.h](test/custom_native_capability_config_CPUID_AVX2.h)
  - [test/custom_native_capability_config_ID_AA64PFR1_EL1.h](test/custom_native_capability_config_ID_AA64PFR1_EL1.h)
  - [test/custom_randombytes_config.h](test/custom_randombytes_config.h)
  - [test/custom_stdlib_config.h](test/custom_stdlib_config.h)
  - [test/custom_zeroize_config.h](test/custom_zeroize_config.h)
  - [test/no_asm_config.h](test/no_asm_config.h)

### `FIPS202`

* FIPS202 SHA-3 Standard: Permutation-Based Hash and Extendable-Output Functions
* Author(s):
  - National Institute of Standards and Technology
* URL: https://csrc.nist.gov/pubs/fips/202/final
* Referenced from:
  - [FIPS202.md](FIPS202.md)
  - [README.md](README.md)

### `FIPS203`

* FIPS 203 Module-Lattice-Based Key-Encapsulation Mechanism Standard
* Author(s):
  - National Institute of Standards and Technology
* URL: https://csrc.nist.gov/pubs/fips/203/final
* Referenced from:
  - [README.md](README.md)
  - [mlkem/mlkem_native.h](mlkem/mlkem_native.h)
  - [mlkem/src/compress.c](mlkem/src/compress.c)
  - [mlkem/src/compress.h](mlkem/src/compress.h)
  - [mlkem/src/fips202/fips202.c](mlkem/src/fips202/fips202.c)
  - [mlkem/src/fips202/fips202x4.c](mlkem/src/fips202/fips202x4.c)
  - [mlkem/src/indcpa.c](mlkem/src/indcpa.c)
  - [mlkem/src/indcpa.h](mlkem/src/indcpa.h)
  - [mlkem/src/kem.c](mlkem/src/kem.c)
  - [mlkem/src/kem.h](mlkem/src/kem.h)
  - [mlkem/src/poly.h](mlkem/src/poly.h)
  - [mlkem/src/poly_k.c](mlkem/src/poly_k.c)
  - [mlkem/src/poly_k.h](mlkem/src/poly_k.h)
  - [mlkem/src/sampling.c](mlkem/src/sampling.c)
  - [mlkem/src/sampling.h](mlkem/src/sampling.h)
  - [mlkem/src/symmetric.h](mlkem/src/symmetric.h)
  - [mlkem/src/verify.h](mlkem/src/verify.h)

### `HYBRID`

* Hybrid scalar/vector implementations of Keccak and SPHINCS+ on AArch64
* Author(s):
  - Hanno Becker
  - Matthias J. Kannwischer
* URL: https://eprint.iacr.org/2022/1243
* Referenced from:
  - [README.md](README.md)
  - [dev/fips202/aarch64/auto.h](dev/fips202/aarch64/auto.h)
  - [dev/fips202/aarch64/src/keccak_f1600_x1_v84a_asm.S](dev/fips202/aarch64/src/keccak_f1600_x1_v84a_asm.S)
  - [dev/fips202/aarch64/src/keccak_f1600_x2_v84a_asm.S](dev/fips202/aarch64/src/keccak_f1600_x2_v84a_asm.S)
  - [mlkem/src/fips202/native/aarch64/auto.h](mlkem/src/fips202/native/aarch64/auto.h)
  - [mlkem/src/fips202/native/aarch64/src/keccak_f1600_x1_v84a_asm.S](mlkem/src/fips202/native/aarch64/src/keccak_f1600_x1_v84a_asm.S)
  - [mlkem/src/fips202/native/aarch64/src/keccak_f1600_x2_v84a_asm.S](mlkem/src/fips202/native/aarch64/src/keccak_f1600_x2_v84a_asm.S)
  - [proofs/hol_light/arm/README.md](proofs/hol_light/arm/README.md)
  - [proofs/hol_light/arm/mlkem/keccak_f1600_x1_v84a.S](proofs/hol_light/arm/mlkem/keccak_f1600_x1_v84a.S)
  - [proofs/hol_light/arm/mlkem/keccak_f1600_x2_v84a.S](proofs/hol_light/arm/mlkem/keccak_f1600_x2_v84a.S)

### `KyberSlash`

* KyberSlash: Exploiting secret-dependent division timings in Kyber implementations
* Author(s):
  - Daniel J. Bernstein
  - Karthikeyan Bhargavan
  - Shivam Bhasin
  - Anupam Chattopadhyay
  - Tee Kiah Chia
  - Matthias J. Kannwischer
  - Franziskus Kiefer
  - Thales Paiva
  - Prasanna Ravi
  - Goutam Tamvada
* URL: https://kyberslash.cr.yp.to/papers.html
* Referenced from:
  - [README.md](README.md)
  - [nix/valgrind/README.md](nix/valgrind/README.md)

### `NeonNTT`

* Neon NTT: Faster Dilithium, Kyber, and Saber on Cortex-A72 and Apple M1
* Author(s):
  - Hanno Becker
  - Vincent Hwang
  - Matthias J. Kannwischer
  - Bo-Yin Yang
  - Shang-Yi Yang
* URL: https://eprint.iacr.org/2021/986
* Referenced from:
  - [dev/aarch64_clean/README.md](dev/aarch64_clean/README.md)
  - [dev/aarch64_clean/src/intt.S](dev/aarch64_clean/src/intt.S)
  - [dev/aarch64_clean/src/ntt.S](dev/aarch64_clean/src/ntt.S)
  - [dev/aarch64_clean/src/polyvec_basemul_acc_montgomery_cached_asm_k2.S](dev/aarch64_clean/src/polyvec_basemul_acc_montgomery_cached_asm_k2.S)
  - [dev/aarch64_clean/src/polyvec_basemul_acc_montgomery_cached_asm_k3.S](dev/aarch64_clean/src/polyvec_basemul_acc_montgomery_cached_asm_k3.S)
  - [dev/aarch64_clean/src/polyvec_basemul_acc_montgomery_cached_asm_k4.S](dev/aarch64_clean/src/polyvec_basemul_acc_montgomery_cached_asm_k4.S)
  - [dev/aarch64_opt/README.md](dev/aarch64_opt/README.md)
  - [dev/aarch64_opt/src/intt.S](dev/aarch64_opt/src/intt.S)
  - [dev/aarch64_opt/src/ntt.S](dev/aarch64_opt/src/ntt.S)
  - [dev/aarch64_opt/src/polyvec_basemul_acc_montgomery_cached_asm_k2.S](dev/aarch64_opt/src/polyvec_basemul_acc_montgomery_cached_asm_k2.S)
  - [dev/aarch64_opt/src/polyvec_basemul_acc_montgomery_cached_asm_k3.S](dev/aarch64_opt/src/polyvec_basemul_acc_montgomery_cached_asm_k3.S)
  - [dev/aarch64_opt/src/polyvec_basemul_acc_montgomery_cached_asm_k4.S](dev/aarch64_opt/src/polyvec_basemul_acc_montgomery_cached_asm_k4.S)
  - [mlkem/src/native/aarch64/README.md](mlkem/src/native/aarch64/README.md)
  - [mlkem/src/native/aarch64/src/intt.S](mlkem/src/native/aarch64/src/intt.S)
  - [mlkem/src/native/aarch64/src/ntt.S](mlkem/src/native/aarch64/src/ntt.S)
  - [mlkem/src/native/aarch64/src/polyvec_basemul_acc_montgomery_cached_asm_k2.S](mlkem/src/native/aarch64/src/polyvec_basemul_acc_montgomery_cached_asm_k2.S)
  - [mlkem/src/native/aarch64/src/polyvec_basemul_acc_montgomery_cached_asm_k3.S](mlkem/src/native/aarch64/src/polyvec_basemul_acc_montgomery_cached_asm_k3.S)
  - [mlkem/src/native/aarch64/src/polyvec_basemul_acc_montgomery_cached_asm_k4.S](mlkem/src/native/aarch64/src/polyvec_basemul_acc_montgomery_cached_asm_k4.S)
  - [mlkem/src/poly.c](mlkem/src/poly.c)
  - [mlkem/src/poly_k.c](mlkem/src/poly_k.c)
  - [proofs/hol_light/arm/mlkem/mlkem_intt.S](proofs/hol_light/arm/mlkem/mlkem_intt.S)
  - [proofs/hol_light/arm/mlkem/mlkem_ntt.S](proofs/hol_light/arm/mlkem/mlkem_ntt.S)
  - [proofs/hol_light/arm/mlkem/mlkem_poly_basemul_acc_montgomery_cached_k2.S](proofs/hol_light/arm/mlkem/mlkem_poly_basemul_acc_montgomery_cached_k2.S)
  - [proofs/hol_light/arm/mlkem/mlkem_poly_basemul_acc_montgomery_cached_k3.S](proofs/hol_light/arm/mlkem/mlkem_poly_basemul_acc_montgomery_cached_k3.S)
  - [proofs/hol_light/arm/mlkem/mlkem_poly_basemul_acc_montgomery_cached_k4.S](proofs/hol_light/arm/mlkem/mlkem_poly_basemul_acc_montgomery_cached_k4.S)

### `REF`

* CRYSTALS-Kyber C reference implementation
* Author(s):
  - Joppe Bos
  - Léo Ducas
  - Eike Kiltz
  - Tancrède Lepoint
  - Vadim Lyubashevsky
  - John Schanck
  - Peter Schwabe
  - Gregor Seiler
  - Damien Stehlé
* URL: https://github.com/pq-crystals/kyber/tree/main/ref
* Referenced from:
  - [README.md](README.md)
  - [REFERENCE.md](REFERENCE.md)
  - [mlkem/src/compress.c](mlkem/src/compress.c)
  - [mlkem/src/compress.h](mlkem/src/compress.h)
  - [mlkem/src/indcpa.c](mlkem/src/indcpa.c)
  - [mlkem/src/kem.c](mlkem/src/kem.c)
  - [mlkem/src/kem.h](mlkem/src/kem.h)
  - [mlkem/src/poly.c](mlkem/src/poly.c)
  - [mlkem/src/poly_k.c](mlkem/src/poly_k.c)
  - [mlkem/src/sampling.c](mlkem/src/sampling.c)
  - [mlkem/src/verify.h](mlkem/src/verify.h)

### `REF_AVX2`

* CRYSTALS-Kyber optimized AVX2 implementation
* Author(s):
  - Joppe Bos
  - Léo Ducas
  - Eike Kiltz
  - Tancrède Lepoint
  - Vadim Lyubashevsky
  - John Schanck
  - Peter Schwabe
  - Gregor Seiler
  - Damien Stehlé
* URL: https://github.com/pq-crystals/kyber/tree/main/avx2
* Referenced from:
  - [dev/x86_64/README.md](dev/x86_64/README.md)
  - [dev/x86_64/src/compress_avx2.c](dev/x86_64/src/compress_avx2.c)
  - [dev/x86_64/src/consts.c](dev/x86_64/src/consts.c)
  - [dev/x86_64/src/consts.h](dev/x86_64/src/consts.h)
  - [dev/x86_64/src/intt.S](dev/x86_64/src/intt.S)
  - [dev/x86_64/src/ntt.S](dev/x86_64/src/ntt.S)
  - [dev/x86_64/src/nttfrombytes.S](dev/x86_64/src/nttfrombytes.S)
  - [dev/x86_64/src/ntttobytes.S](dev/x86_64/src/ntttobytes.S)
  - [dev/x86_64/src/nttunpack.S](dev/x86_64/src/nttunpack.S)
  - [dev/x86_64/src/reduce.S](dev/x86_64/src/reduce.S)
  - [dev/x86_64/src/tomont.S](dev/x86_64/src/tomont.S)
  - [mlkem/src/native/x86_64/src/compress_avx2.c](mlkem/src/native/x86_64/src/compress_avx2.c)
  - [mlkem/src/native/x86_64/src/consts.c](mlkem/src/native/x86_64/src/consts.c)
  - [mlkem/src/native/x86_64/src/consts.h](mlkem/src/native/x86_64/src/consts.h)
  - [mlkem/src/native/x86_64/src/intt.S](mlkem/src/native/x86_64/src/intt.S)
  - [mlkem/src/native/x86_64/src/ntt.S](mlkem/src/native/x86_64/src/ntt.S)
  - [mlkem/src/native/x86_64/src/nttfrombytes.S](mlkem/src/native/x86_64/src/nttfrombytes.S)
  - [mlkem/src/native/x86_64/src/ntttobytes.S](mlkem/src/native/x86_64/src/ntttobytes.S)
  - [mlkem/src/native/x86_64/src/nttunpack.S](mlkem/src/native/x86_64/src/nttunpack.S)
  - [mlkem/src/native/x86_64/src/reduce.S](mlkem/src/native/x86_64/src/reduce.S)
  - [mlkem/src/native/x86_64/src/tomont.S](mlkem/src/native/x86_64/src/tomont.S)

### `SLOTHY`

* SLOTHY superoptimizer
* Author(s):
  - Amin Abdulrahman
  - Hanno Becker
  - Matthias J. Kannwischer
  - Fabien Klein
* URL: https://github.com/slothy-optimizer/slothy/
* Referenced from:
  - [dev/README.md](dev/README.md)
  - [proofs/hol_light/arm/README.md](proofs/hol_light/arm/README.md)

### `SLOTHY_Paper`

* Fast and Clean: Auditable high-performance assembly via constraint solving
* Author(s):
  - Amin Abdulrahman
  - Hanno Becker
  - Matthias J. Kannwischer
  - Fabien Klein
* URL: https://eprint.iacr.org/2022/1303
* Referenced from:
  - [README.md](README.md)
  - [dev/README.md](dev/README.md)
  - [dev/aarch64_clean/README.md](dev/aarch64_clean/README.md)
  - [dev/aarch64_clean/src/intt.S](dev/aarch64_clean/src/intt.S)
  - [dev/aarch64_clean/src/ntt.S](dev/aarch64_clean/src/ntt.S)
  - [dev/aarch64_opt/README.md](dev/aarch64_opt/README.md)
  - [dev/aarch64_opt/src/intt.S](dev/aarch64_opt/src/intt.S)
  - [dev/aarch64_opt/src/ntt.S](dev/aarch64_opt/src/ntt.S)
  - [mlkem/src/native/aarch64/README.md](mlkem/src/native/aarch64/README.md)
  - [mlkem/src/native/aarch64/src/intt.S](mlkem/src/native/aarch64/src/intt.S)
  - [mlkem/src/native/aarch64/src/ntt.S](mlkem/src/native/aarch64/src/ntt.S)
  - [proofs/hol_light/arm/mlkem/mlkem_intt.S](proofs/hol_light/arm/mlkem/mlkem_intt.S)
  - [proofs/hol_light/arm/mlkem/mlkem_ntt.S](proofs/hol_light/arm/mlkem/mlkem_ntt.S)

### `clangover`

* clangover
* Author(s):
  - Antoon Purnal
* URL: https://github.com/antoonpurnal/clangover
* Referenced from:
  - [README.md](README.md)

### `libmceliece`

* libmceliece implementation of Classic McEliece
* Author(s):
  - Daniel J. Bernstein
  - Tung Chou
* URL: https://lib.mceliece.org/
* Referenced from:
  - [mlkem/src/verify.h](mlkem/src/verify.h)

### `m1cycles`

* Cycle counting on Apple M1
* Author(s):
  - Dougall Johnson
* URL: https://gist.github.com/dougallj/5bafb113492047c865c0c8cfbc930155#file-m1_robsize-c-L390
* Referenced from:
  - [test/hal/hal.c](test/hal/hal.c)

### `mupq`

* Common files for pqm4, pqm3, pqriscv
* Author(s):
  - Kannwischer et. al
* URL: https://github.com/mupq/mupq
* Referenced from:
  - [mlkem/src/fips202/fips202.c](mlkem/src/fips202/fips202.c)
  - [mlkem/src/fips202/keccakf1600.c](mlkem/src/fips202/keccakf1600.c)

### `optblocker`

* PQC forum post on opt-blockers using volatile globals
* Author(s):
  - Daniel J. Bernstein
* URL: https://groups.google.com/a/list.nist.gov/g/pqc-forum/c/hqbtIGFKIpU/m/H14H0wOlBgAJ
* Referenced from:
  - [mlkem/src/verify.h](mlkem/src/verify.h)

### `supercop`

* SUPERCOP benchmarking framework
* Author(s):
  - Daniel J. Bernstein
* URL: http://bench.cr.yp.to/supercop.html
* Referenced from:
  - [mlkem/src/fips202/fips202.c](mlkem/src/fips202/fips202.c)
  - [mlkem/src/fips202/keccakf1600.c](mlkem/src/fips202/keccakf1600.c)

### `surf`

* SURF: Simple Unpredictable Random Function
* Author(s):
  - Daniel J. Bernstein
* URL: https://cr.yp.to/papers.html#surf
* Referenced from:
  - [test/notrandombytes/notrandombytes.c](test/notrandombytes/notrandombytes.c)
  - [test/notrandombytes/notrandombytes.h](test/notrandombytes/notrandombytes.h)

### `tiny_sha3`

* tiny_sha3
* Author(s):
  - Markku-Juhani O. Saarinen
* URL: https://github.com/mjosaarinen/tiny_sha3
* Referenced from:
  - [README.md](README.md)
  - [examples/bring_your_own_fips202/README.md](examples/bring_your_own_fips202/README.md)
  - [examples/bring_your_own_fips202/custom_fips202/README.md](examples/bring_your_own_fips202/custom_fips202/README.md)
  - [examples/custom_backend/README.md](examples/custom_backend/README.md)

### `tweetfips`

* 'tweetfips202' FIPS202 implementation
* Author(s):
  - Gilles Van Assche
  - Daniel J. Bernstein
  - Peter Schwabe
* URL: https://keccak.team/2015/tweetfips202.html
* Referenced from:
  - [mlkem/src/fips202/fips202.c](mlkem/src/fips202/fips202.c)
  - [mlkem/src/fips202/keccakf1600.c](mlkem/src/fips202/keccakf1600.c)
