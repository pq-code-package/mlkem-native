/*
 * Copyright (c) 2024-2025 The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0
 */

/*
 * WARNING: This file is auto-generated from scripts/autogen
 *          Do not modify it directly.
 */

/*
 * Monolithic compilation unit bundling all compilation units within
 * mlkem-native
 */

#include "mlkem/sys.h"

#include "mlkem/compress.c"
#include "mlkem/debug.c"
#include "mlkem/fips202/fips202.c"
#include "mlkem/fips202/fips202x4.c"
#include "mlkem/fips202/keccakf1600.c"
#include "mlkem/indcpa.c"
#include "mlkem/kem.c"
#include "mlkem/poly.c"
#include "mlkem/poly_k.c"
#include "mlkem/sampling.c"
#include "mlkem/verify.c"
#include "mlkem/zetas.c"
#if defined(MLKEM_NATIVE_MONOBUILD_WITH_NATIVE_ARITH)
#if defined(SYS_AARCH64)
#include "mlkem/native/aarch64/src/aarch64_zetas.c"
#include "mlkem/native/aarch64/src/rej_uniform_table.c"
#endif /* SYS_AARCH64 */
#if defined(SYS_X86_64)
#include "mlkem/native/x86_64/src/basemul.c"
#include "mlkem/native/x86_64/src/compress_avx2.c"
#include "mlkem/native/x86_64/src/consts.c"
#include "mlkem/native/x86_64/src/rej_uniform_avx2.c"
#include "mlkem/native/x86_64/src/rej_uniform_table.c"
#endif /* SYS_X86_64 */
#endif /* MLKEM_NATIVE_MONOBUILD_WITH_NATIVE_ARITH */
#if defined(MLKEM_NATIVE_MONOBUILD_WITH_NATIVE_FIPS202)
#if defined(SYS_AARCH64)
#include "mlkem/fips202/native/aarch64/src/keccakf1600_round_constants.c"
#endif /* SYS_AARCH64 */
#if defined(SYS_X86_64)
#include "mlkem/fips202/native/x86_64/src/KeccakP-1600-times4-SIMD256.c"
#endif /* SYS_X86_64 */
#endif /* MLKEM_NATIVE_MONOBUILD_WITH_NATIVE_FIPS202 */


/*
 * Undefine macros from MLKEM_K-specific files
 */

/* mlkem/common.h */
#undef MLKEM_ASM_NAMESPACE
#undef MLKEM_NAMESPACE
#undef MLKEM_NAMESPACE_K
#undef MLKEM_NATIVE_ARITH_BACKEND_NAME
#undef MLKEM_NATIVE_COMMON_H
#undef MLKEM_NATIVE_EMPTY_CU
#undef MLKEM_NATIVE_FIPS202_BACKEND_NAME
#undef MLKEM_NATIVE_INTERNAL_API
#undef MLKEM_NATIVE_MAKE_NAMESPACE
#undef MLKEM_NATIVE_MAKE_NAMESPACE_
#undef MLKEM_NATIVE_MAKE_NAMESPACE_K
#undef MLKEM_NATIVE_MAKE_NAMESPACE_K_
#undef PREFIX_UNDERSCORE
#undef PREFIX_UNDERSCORE_
/* mlkem/config.h */
#undef MLKEM_DEFAULT_NAMESPACE_PREFIX
#undef MLKEM_K
#undef MLKEM_NAMESPACE_PREFIX
#undef MLKEM_NATIVE_ARITH_BACKEND_FILE
#undef MLKEM_NATIVE_CONFIG_H
#undef MLKEM_NATIVE_FIPS202_BACKEND_FILE
/* mlkem/indcpa.h */
#undef MLKEM_NATIVE_INDCPA_H
#undef gen_matrix
#undef indcpa_dec
#undef indcpa_enc
#undef indcpa_keypair_derand
/* mlkem/kem.h */
#undef MLKEM_NATIVE_KEM_H
#undef crypto_kem_dec
#undef crypto_kem_enc
#undef crypto_kem_enc_derand
#undef crypto_kem_keypair
#undef crypto_kem_keypair_derand
/* mlkem/mlkem_native.h */
#undef BUILD_INFO_CONCAT2
#undef BUILD_INFO_CONCAT2_
#undef BUILD_INFO_CONCAT3
#undef BUILD_INFO_CONCAT3_
#undef BUILD_INFO_LVL
#undef BUILD_INFO_NAMESPACE
#undef CRYPTO_BYTES
#undef CRYPTO_CIPHERTEXTBYTES
#undef CRYPTO_PUBLICKEYBYTES
#undef CRYPTO_SECRETKEYBYTES
#undef CRYPTO_SYMBYTES
#undef MLKEM1024_BYTES
#undef MLKEM1024_CIPHERTEXTBYTES
#undef MLKEM1024_PUBLICKEYBYTES
#undef MLKEM1024_SECRETKEYBYTES
#undef MLKEM1024_SYMBYTES
#undef MLKEM512_BYTES
#undef MLKEM512_CIPHERTEXTBYTES
#undef MLKEM512_PUBLICKEYBYTES
#undef MLKEM512_SECRETKEYBYTES
#undef MLKEM512_SYMBYTES
#undef MLKEM768_BYTES
#undef MLKEM768_CIPHERTEXTBYTES
#undef MLKEM768_PUBLICKEYBYTES
#undef MLKEM768_SECRETKEYBYTES
#undef MLKEM768_SYMBYTES
#undef MLKEM_BYTES
#undef MLKEM_CIPHERTEXTBYTES
#undef MLKEM_CIPHERTEXTBYTES_
#undef MLKEM_NATIVE_H
#undef MLKEM_PUBLICKEYBYTES
#undef MLKEM_PUBLICKEYBYTES_
#undef MLKEM_SECRETKEYBYTES
#undef MLKEM_SECRETKEYBYTES_
#undef MLKEM_SYMBYTES
#undef crypto_kem_dec
#undef crypto_kem_enc
#undef crypto_kem_enc_derand
#undef crypto_kem_keypair
#undef crypto_kem_keypair_derand
/* mlkem/params.h */
#undef MLKEM_DU
#undef MLKEM_DV
#undef MLKEM_ETA1
#undef MLKEM_ETA2
#undef MLKEM_INDCCA_CIPHERTEXTBYTES
#undef MLKEM_INDCCA_PUBLICKEYBYTES
#undef MLKEM_INDCCA_SECRETKEYBYTES
#undef MLKEM_INDCPA_BYTES
#undef MLKEM_INDCPA_MSGBYTES
#undef MLKEM_INDCPA_PUBLICKEYBYTES
#undef MLKEM_INDCPA_SECRETKEYBYTES
#undef MLKEM_LVL
#undef MLKEM_N
#undef MLKEM_NATIVE_PARAMS_H
#undef MLKEM_POLYBYTES
#undef MLKEM_POLYCOMPRESSEDBYTES_D10
#undef MLKEM_POLYCOMPRESSEDBYTES_D11
#undef MLKEM_POLYCOMPRESSEDBYTES_D4
#undef MLKEM_POLYCOMPRESSEDBYTES_D5
#undef MLKEM_POLYCOMPRESSEDBYTES_DU
#undef MLKEM_POLYCOMPRESSEDBYTES_DV
#undef MLKEM_POLYVECBYTES
#undef MLKEM_POLYVECCOMPRESSEDBYTES_DU
#undef MLKEM_Q
#undef MLKEM_Q_HALF
#undef MLKEM_SSBYTES
#undef MLKEM_SYMBYTES
#undef UINT12_LIMIT
/* mlkem/poly_k.h */
#undef MLKEM_NATIVE_POLY_K_H
#undef poly_compress_du
#undef poly_compress_dv
#undef poly_decompress_du
#undef poly_decompress_dv
#undef poly_getnoise_eta1122_4x
#undef poly_getnoise_eta1_4x
#undef poly_getnoise_eta2
#undef poly_getnoise_eta2_4x
#undef polyvec
#undef polyvec_add
#undef polyvec_basemul_acc_montgomery
#undef polyvec_basemul_acc_montgomery_cached
#undef polyvec_compress_du
#undef polyvec_decompress_du
#undef polyvec_frombytes
#undef polyvec_invntt_tomont
#undef polyvec_mulcache
#undef polyvec_mulcache_compute
#undef polyvec_ntt
#undef polyvec_reduce
#undef polyvec_tobytes
#undef polyvec_tomont
