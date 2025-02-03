/*
 * Copyright (c) 2024 The mlkem-native project authors
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
#include "mlkem/native/aarch64/src/aarch64_zetas.c"
#include "mlkem/native/aarch64/src/rej_uniform_table.c"
#include "mlkem/native/x86_64/src/basemul.c"
#include "mlkem/native/x86_64/src/compress_avx2.c"
#include "mlkem/native/x86_64/src/consts.c"
#include "mlkem/native/x86_64/src/rej_uniform_avx2.c"
#include "mlkem/native/x86_64/src/rej_uniform_table.c"
#endif
#if defined(MLKEM_NATIVE_MONOBUILD_WITH_NATIVE_FIPS202)
#include "mlkem/fips202/native/aarch64/src/keccakf1600_round_constants.c"
#include "mlkem/fips202/native/x86_64/src/KeccakP-1600-times4-SIMD256.c"
#endif


/*
 * Undo all #define directives from *.[ch] files (MLKEM_K-specific files)
 */

/* mlkem/common.h */
#if defined(MLKEM_ASM_NAMESPACE)
#undef MLKEM_ASM_NAMESPACE
#endif

/* mlkem/common.h */
#if defined(MLKEM_NAMESPACE)
#undef MLKEM_NAMESPACE
#endif

/* mlkem/common.h */
#if defined(MLKEM_NAMESPACE_K)
#undef MLKEM_NAMESPACE_K
#endif

/* mlkem/common.h */
#if defined(MLKEM_NATIVE_ARITH_BACKEND_NAME)
#undef MLKEM_NATIVE_ARITH_BACKEND_NAME
#endif

/* mlkem/common.h */
#if defined(MLKEM_NATIVE_COMMON_H)
#undef MLKEM_NATIVE_COMMON_H
#endif

/* mlkem/common.h */
#if defined(MLKEM_NATIVE_EMPTY_CU)
#undef MLKEM_NATIVE_EMPTY_CU
#endif

/* mlkem/common.h */
#if defined(MLKEM_NATIVE_FIPS202_BACKEND_NAME)
#undef MLKEM_NATIVE_FIPS202_BACKEND_NAME
#endif

/* mlkem/common.h */
#if defined(MLKEM_NATIVE_INTERNAL_API)
#undef MLKEM_NATIVE_INTERNAL_API
#endif

/* mlkem/common.h */
#if defined(MLKEM_NATIVE_MAKE_NAMESPACE)
#undef MLKEM_NATIVE_MAKE_NAMESPACE
#endif

/* mlkem/common.h */
#if defined(MLKEM_NATIVE_MAKE_NAMESPACE_)
#undef MLKEM_NATIVE_MAKE_NAMESPACE_
#endif

/* mlkem/common.h */
#if defined(MLKEM_NATIVE_MAKE_NAMESPACE_K)
#undef MLKEM_NATIVE_MAKE_NAMESPACE_K
#endif

/* mlkem/common.h */
#if defined(MLKEM_NATIVE_MAKE_NAMESPACE_K_)
#undef MLKEM_NATIVE_MAKE_NAMESPACE_K_
#endif

/* mlkem/common.h */
#if defined(PREFIX_UNDERSCORE)
#undef PREFIX_UNDERSCORE
#endif

/* mlkem/common.h */
#if defined(PREFIX_UNDERSCORE_)
#undef PREFIX_UNDERSCORE_
#endif

/* mlkem/config.h */
#if defined(MLKEM_DEFAULT_NAMESPACE_PREFIX)
#undef MLKEM_DEFAULT_NAMESPACE_PREFIX
#endif

/* mlkem/config.h */
#if defined(MLKEM_K)
#undef MLKEM_K
#endif

/* mlkem/config.h */
#if defined(MLKEM_NAMESPACE_PREFIX)
#undef MLKEM_NAMESPACE_PREFIX
#endif

/* mlkem/config.h */
#if defined(MLKEM_NATIVE_ARITH_BACKEND_FILE)
#undef MLKEM_NATIVE_ARITH_BACKEND_FILE
#endif

/* mlkem/config.h */
#if defined(MLKEM_NATIVE_CONFIG_H)
#undef MLKEM_NATIVE_CONFIG_H
#endif

/* mlkem/config.h */
#if defined(MLKEM_NATIVE_FIPS202_BACKEND_FILE)
#undef MLKEM_NATIVE_FIPS202_BACKEND_FILE
#endif

/* mlkem/indcpa.c */
#if defined(matvec_mul)
#undef matvec_mul
#endif

/* mlkem/indcpa.c */
#if defined(pack_ciphertext)
#undef pack_ciphertext
#endif

/* mlkem/indcpa.c */
#if defined(pack_pk)
#undef pack_pk
#endif

/* mlkem/indcpa.c */
#if defined(pack_sk)
#undef pack_sk
#endif

/* mlkem/indcpa.c */
#if defined(poly_permute_bitrev_to_custom)
#undef poly_permute_bitrev_to_custom
#endif

/* mlkem/indcpa.c */
#if defined(unpack_ciphertext)
#undef unpack_ciphertext
#endif

/* mlkem/indcpa.c */
#if defined(unpack_pk)
#undef unpack_pk
#endif

/* mlkem/indcpa.c */
#if defined(unpack_sk)
#undef unpack_sk
#endif

/* mlkem/indcpa.h */
#if defined(MLKEM_NATIVE_INDCPA_H)
#undef MLKEM_NATIVE_INDCPA_H
#endif

/* mlkem/indcpa.h */
#if defined(gen_matrix)
#undef gen_matrix
#endif

/* mlkem/indcpa.h */
#if defined(indcpa_dec)
#undef indcpa_dec
#endif

/* mlkem/indcpa.h */
#if defined(indcpa_enc)
#undef indcpa_enc
#endif

/* mlkem/indcpa.h */
#if defined(indcpa_keypair_derand)
#undef indcpa_keypair_derand
#endif

/* mlkem/kem.c */
#if defined(check_pk)
#undef check_pk
#endif

/* mlkem/kem.c */
#if defined(check_sk)
#undef check_sk
#endif

/* mlkem/kem.h */
#if defined(MLKEM_NATIVE_KEM_H)
#undef MLKEM_NATIVE_KEM_H
#endif

/* mlkem/kem.h */
#if defined(crypto_kem_dec)
#undef crypto_kem_dec
#endif

/* mlkem/kem.h */
#if defined(crypto_kem_enc)
#undef crypto_kem_enc
#endif

/* mlkem/kem.h */
#if defined(crypto_kem_enc_derand)
#undef crypto_kem_enc_derand
#endif

/* mlkem/kem.h */
#if defined(crypto_kem_keypair)
#undef crypto_kem_keypair
#endif

/* mlkem/kem.h */
#if defined(crypto_kem_keypair_derand)
#undef crypto_kem_keypair_derand
#endif

/* mlkem/mlkem_native.h */
#if defined(BUILD_INFO_CONCAT2)
#undef BUILD_INFO_CONCAT2
#endif

/* mlkem/mlkem_native.h */
#if defined(BUILD_INFO_CONCAT2_)
#undef BUILD_INFO_CONCAT2_
#endif

/* mlkem/mlkem_native.h */
#if defined(BUILD_INFO_CONCAT3)
#undef BUILD_INFO_CONCAT3
#endif

/* mlkem/mlkem_native.h */
#if defined(BUILD_INFO_CONCAT3_)
#undef BUILD_INFO_CONCAT3_
#endif

/* mlkem/mlkem_native.h */
#if defined(BUILD_INFO_LVL)
#undef BUILD_INFO_LVL
#endif

/* mlkem/mlkem_native.h */
#if defined(BUILD_INFO_NAMESPACE)
#undef BUILD_INFO_NAMESPACE
#endif

/* mlkem/mlkem_native.h */
#if defined(CRYPTO_BYTES)
#undef CRYPTO_BYTES
#endif

/* mlkem/mlkem_native.h */
#if defined(CRYPTO_CIPHERTEXTBYTES)
#undef CRYPTO_CIPHERTEXTBYTES
#endif

/* mlkem/mlkem_native.h */
#if defined(CRYPTO_PUBLICKEYBYTES)
#undef CRYPTO_PUBLICKEYBYTES
#endif

/* mlkem/mlkem_native.h */
#if defined(CRYPTO_SECRETKEYBYTES)
#undef CRYPTO_SECRETKEYBYTES
#endif

/* mlkem/mlkem_native.h */
#if defined(CRYPTO_SYMBYTES)
#undef CRYPTO_SYMBYTES
#endif

/* mlkem/mlkem_native.h */
#if defined(MLKEM1024_BYTES)
#undef MLKEM1024_BYTES
#endif

/* mlkem/mlkem_native.h */
#if defined(MLKEM1024_CIPHERTEXTBYTES)
#undef MLKEM1024_CIPHERTEXTBYTES
#endif

/* mlkem/mlkem_native.h */
#if defined(MLKEM1024_PUBLICKEYBYTES)
#undef MLKEM1024_PUBLICKEYBYTES
#endif

/* mlkem/mlkem_native.h */
#if defined(MLKEM1024_SECRETKEYBYTES)
#undef MLKEM1024_SECRETKEYBYTES
#endif

/* mlkem/mlkem_native.h */
#if defined(MLKEM1024_SYMBYTES)
#undef MLKEM1024_SYMBYTES
#endif

/* mlkem/mlkem_native.h */
#if defined(MLKEM512_BYTES)
#undef MLKEM512_BYTES
#endif

/* mlkem/mlkem_native.h */
#if defined(MLKEM512_CIPHERTEXTBYTES)
#undef MLKEM512_CIPHERTEXTBYTES
#endif

/* mlkem/mlkem_native.h */
#if defined(MLKEM512_PUBLICKEYBYTES)
#undef MLKEM512_PUBLICKEYBYTES
#endif

/* mlkem/mlkem_native.h */
#if defined(MLKEM512_SECRETKEYBYTES)
#undef MLKEM512_SECRETKEYBYTES
#endif

/* mlkem/mlkem_native.h */
#if defined(MLKEM512_SYMBYTES)
#undef MLKEM512_SYMBYTES
#endif

/* mlkem/mlkem_native.h */
#if defined(MLKEM768_BYTES)
#undef MLKEM768_BYTES
#endif

/* mlkem/mlkem_native.h */
#if defined(MLKEM768_CIPHERTEXTBYTES)
#undef MLKEM768_CIPHERTEXTBYTES
#endif

/* mlkem/mlkem_native.h */
#if defined(MLKEM768_PUBLICKEYBYTES)
#undef MLKEM768_PUBLICKEYBYTES
#endif

/* mlkem/mlkem_native.h */
#if defined(MLKEM768_SECRETKEYBYTES)
#undef MLKEM768_SECRETKEYBYTES
#endif

/* mlkem/mlkem_native.h */
#if defined(MLKEM768_SYMBYTES)
#undef MLKEM768_SYMBYTES
#endif

/* mlkem/mlkem_native.h */
#if defined(MLKEM_BYTES)
#undef MLKEM_BYTES
#endif

/* mlkem/mlkem_native.h */
#if defined(MLKEM_CIPHERTEXTBYTES)
#undef MLKEM_CIPHERTEXTBYTES
#endif

/* mlkem/mlkem_native.h */
#if defined(MLKEM_CIPHERTEXTBYTES_)
#undef MLKEM_CIPHERTEXTBYTES_
#endif

/* mlkem/mlkem_native.h */
#if defined(MLKEM_NATIVE_H)
#undef MLKEM_NATIVE_H
#endif

/* mlkem/mlkem_native.h */
#if defined(MLKEM_PUBLICKEYBYTES)
#undef MLKEM_PUBLICKEYBYTES
#endif

/* mlkem/mlkem_native.h */
#if defined(MLKEM_PUBLICKEYBYTES_)
#undef MLKEM_PUBLICKEYBYTES_
#endif

/* mlkem/mlkem_native.h */
#if defined(MLKEM_SECRETKEYBYTES)
#undef MLKEM_SECRETKEYBYTES
#endif

/* mlkem/mlkem_native.h */
#if defined(MLKEM_SECRETKEYBYTES_)
#undef MLKEM_SECRETKEYBYTES_
#endif

/* mlkem/mlkem_native.h */
#if defined(MLKEM_SYMBYTES)
#undef MLKEM_SYMBYTES
#endif

/* mlkem/mlkem_native.h */
#if defined(crypto_kem_dec)
#undef crypto_kem_dec
#endif

/* mlkem/mlkem_native.h */
#if defined(crypto_kem_enc)
#undef crypto_kem_enc
#endif

/* mlkem/mlkem_native.h */
#if defined(crypto_kem_enc_derand)
#undef crypto_kem_enc_derand
#endif

/* mlkem/mlkem_native.h */
#if defined(crypto_kem_keypair)
#undef crypto_kem_keypair
#endif

/* mlkem/mlkem_native.h */
#if defined(crypto_kem_keypair_derand)
#undef crypto_kem_keypair_derand
#endif

/* mlkem/params.h */
#if defined(HALF_Q)
#undef HALF_Q
#endif

/* mlkem/params.h */
#if defined(KECCAK_WAY)
#undef KECCAK_WAY
#endif

/* mlkem/params.h */
#if defined(MLKEM_DU)
#undef MLKEM_DU
#endif

/* mlkem/params.h */
#if defined(MLKEM_DV)
#undef MLKEM_DV
#endif

/* mlkem/params.h */
#if defined(MLKEM_ETA1)
#undef MLKEM_ETA1
#endif

/* mlkem/params.h */
#if defined(MLKEM_ETA2)
#undef MLKEM_ETA2
#endif

/* mlkem/params.h */
#if defined(MLKEM_INDCCA_CIPHERTEXTBYTES)
#undef MLKEM_INDCCA_CIPHERTEXTBYTES
#endif

/* mlkem/params.h */
#if defined(MLKEM_INDCCA_PUBLICKEYBYTES)
#undef MLKEM_INDCCA_PUBLICKEYBYTES
#endif

/* mlkem/params.h */
#if defined(MLKEM_INDCCA_SECRETKEYBYTES)
#undef MLKEM_INDCCA_SECRETKEYBYTES
#endif

/* mlkem/params.h */
#if defined(MLKEM_INDCPA_BYTES)
#undef MLKEM_INDCPA_BYTES
#endif

/* mlkem/params.h */
#if defined(MLKEM_INDCPA_MSGBYTES)
#undef MLKEM_INDCPA_MSGBYTES
#endif

/* mlkem/params.h */
#if defined(MLKEM_INDCPA_PUBLICKEYBYTES)
#undef MLKEM_INDCPA_PUBLICKEYBYTES
#endif

/* mlkem/params.h */
#if defined(MLKEM_INDCPA_SECRETKEYBYTES)
#undef MLKEM_INDCPA_SECRETKEYBYTES
#endif

/* mlkem/params.h */
#if defined(MLKEM_LVL)
#undef MLKEM_LVL
#endif

/* mlkem/params.h */
#if defined(MLKEM_N)
#undef MLKEM_N
#endif

/* mlkem/params.h */
#if defined(MLKEM_NATIVE_PARAMS_H)
#undef MLKEM_NATIVE_PARAMS_H
#endif

/* mlkem/params.h */
#if defined(MLKEM_POLYBYTES)
#undef MLKEM_POLYBYTES
#endif

/* mlkem/params.h */
#if defined(MLKEM_POLYCOMPRESSEDBYTES_D10)
#undef MLKEM_POLYCOMPRESSEDBYTES_D10
#endif

/* mlkem/params.h */
#if defined(MLKEM_POLYCOMPRESSEDBYTES_D11)
#undef MLKEM_POLYCOMPRESSEDBYTES_D11
#endif

/* mlkem/params.h */
#if defined(MLKEM_POLYCOMPRESSEDBYTES_D4)
#undef MLKEM_POLYCOMPRESSEDBYTES_D4
#endif

/* mlkem/params.h */
#if defined(MLKEM_POLYCOMPRESSEDBYTES_D5)
#undef MLKEM_POLYCOMPRESSEDBYTES_D5
#endif

/* mlkem/params.h */
#if defined(MLKEM_POLYCOMPRESSEDBYTES_DU)
#undef MLKEM_POLYCOMPRESSEDBYTES_DU
#endif

/* mlkem/params.h */
#if defined(MLKEM_POLYCOMPRESSEDBYTES_DV)
#undef MLKEM_POLYCOMPRESSEDBYTES_DV
#endif

/* mlkem/params.h */
#if defined(MLKEM_POLYVECBYTES)
#undef MLKEM_POLYVECBYTES
#endif

/* mlkem/params.h */
#if defined(MLKEM_POLYVECCOMPRESSEDBYTES_DU)
#undef MLKEM_POLYVECCOMPRESSEDBYTES_DU
#endif

/* mlkem/params.h */
#if defined(MLKEM_Q)
#undef MLKEM_Q
#endif

/* mlkem/params.h */
#if defined(MLKEM_SSBYTES)
#undef MLKEM_SSBYTES
#endif

/* mlkem/params.h */
#if defined(MLKEM_SYMBYTES)
#undef MLKEM_SYMBYTES
#endif

/* mlkem/params.h */
#if defined(UINT12_LIMIT)
#undef UINT12_LIMIT
#endif

/* mlkem/poly_k.c */
#if defined(poly_cbd_eta1)
#undef poly_cbd_eta1
#endif

/* mlkem/poly_k.c */
#if defined(poly_cbd_eta2)
#undef poly_cbd_eta2
#endif

/* mlkem/poly_k.h */
#if defined(MLKEM_NATIVE_POLY_K_H)
#undef MLKEM_NATIVE_POLY_K_H
#endif

/* mlkem/poly_k.h */
#if defined(poly_compress_du)
#undef poly_compress_du
#endif

/* mlkem/poly_k.h */
#if defined(poly_compress_dv)
#undef poly_compress_dv
#endif

/* mlkem/poly_k.h */
#if defined(poly_decompress_du)
#undef poly_decompress_du
#endif

/* mlkem/poly_k.h */
#if defined(poly_decompress_dv)
#undef poly_decompress_dv
#endif

/* mlkem/poly_k.h */
#if defined(poly_getnoise_eta1122_4x)
#undef poly_getnoise_eta1122_4x
#endif

/* mlkem/poly_k.h */
#if defined(poly_getnoise_eta1_4x)
#undef poly_getnoise_eta1_4x
#endif

/* mlkem/poly_k.h */
#if defined(poly_getnoise_eta2)
#undef poly_getnoise_eta2
#endif

/* mlkem/poly_k.h */
#if defined(poly_getnoise_eta2_4x)
#undef poly_getnoise_eta2_4x
#endif

/* mlkem/poly_k.h */
#if defined(polyvec)
#undef polyvec
#endif

/* mlkem/poly_k.h */
#if defined(polyvec_add)
#undef polyvec_add
#endif

/* mlkem/poly_k.h */
#if defined(polyvec_basemul_acc_montgomery)
#undef polyvec_basemul_acc_montgomery
#endif

/* mlkem/poly_k.h */
#if defined(polyvec_basemul_acc_montgomery_cached)
#undef polyvec_basemul_acc_montgomery_cached
#endif

/* mlkem/poly_k.h */
#if defined(polyvec_compress_du)
#undef polyvec_compress_du
#endif

/* mlkem/poly_k.h */
#if defined(polyvec_decompress_du)
#undef polyvec_decompress_du
#endif

/* mlkem/poly_k.h */
#if defined(polyvec_frombytes)
#undef polyvec_frombytes
#endif

/* mlkem/poly_k.h */
#if defined(polyvec_invntt_tomont)
#undef polyvec_invntt_tomont
#endif

/* mlkem/poly_k.h */
#if defined(polyvec_mulcache)
#undef polyvec_mulcache
#endif

/* mlkem/poly_k.h */
#if defined(polyvec_mulcache_compute)
#undef polyvec_mulcache_compute
#endif

/* mlkem/poly_k.h */
#if defined(polyvec_ntt)
#undef polyvec_ntt
#endif

/* mlkem/poly_k.h */
#if defined(polyvec_reduce)
#undef polyvec_reduce
#endif

/* mlkem/poly_k.h */
#if defined(polyvec_tobytes)
#undef polyvec_tobytes
#endif

/* mlkem/poly_k.h */
#if defined(polyvec_tomont)
#undef polyvec_tomont
#endif


#if !defined(MLKEM_NATIVE_MONOBUILD_KEEP_SHARED_HEADERS)

/*
 * Undo all #define directives from *.[ch] files (MLKEM_K-generic files)
 */

/* mlkem/arith_backend.h */
#if defined(MLKEM_NATIVE_ARITH_BACKEND_H)
#undef MLKEM_NATIVE_ARITH_BACKEND_H
#endif

/* mlkem/cbmc.h */
#if defined(CBMC_CONCAT)
#undef CBMC_CONCAT
#endif

/* mlkem/cbmc.h */
#if defined(CBMC_CONCAT_)
#undef CBMC_CONCAT_
#endif

/* mlkem/cbmc.h */
#if defined(EXISTS)
#undef EXISTS
#endif

/* mlkem/cbmc.h */
#if defined(MLKEM_NATIVE_CBMC_H)
#undef MLKEM_NATIVE_CBMC_H
#endif

/* mlkem/cbmc.h */
#if defined(__contract__)
#undef __contract__
#endif

/* mlkem/cbmc.h */
#if defined(__loop__)
#undef __loop__
#endif

/* mlkem/cbmc.h */
#if defined(array_abs_bound)
#undef array_abs_bound
#endif

/* mlkem/cbmc.h */
#if defined(array_bound)
#undef array_bound
#endif

/* mlkem/cbmc.h */
#if defined(array_bound_core)
#undef array_bound_core
#endif

/* mlkem/cbmc.h */
#if defined(assigns)
#undef assigns
#endif

/* mlkem/cbmc.h */
#if defined(assume)
#undef assume
#endif

/* mlkem/cbmc.h */
#if defined(cassert)
#undef cassert
#endif

/* mlkem/cbmc.h */
#if defined(decreases)
#undef decreases
#endif

/* mlkem/cbmc.h */
#if defined(ensures)
#undef ensures
#endif

/* mlkem/cbmc.h */
#if defined(forall)
#undef forall
#endif

/* mlkem/cbmc.h */
#if defined(invariant)
#undef invariant
#endif

/* mlkem/cbmc.h */
#if defined(loop_entry)
#undef loop_entry
#endif

/* mlkem/cbmc.h */
#if defined(memory_no_alias)
#undef memory_no_alias
#endif

/* mlkem/cbmc.h */
#if defined(memory_slice)
#undef memory_slice
#endif

/* mlkem/cbmc.h */
#if defined(object_whole)
#undef object_whole
#endif

/* mlkem/cbmc.h */
#if defined(old)
#undef old
#endif

/* mlkem/cbmc.h */
#if defined(readable)
#undef readable
#endif

/* mlkem/cbmc.h */
#if defined(requires)
#undef requires
#endif

/* mlkem/cbmc.h */
#if defined(return_value)
#undef return_value
#endif

/* mlkem/cbmc.h */
#if defined(same_object)
#undef same_object
#endif

/* mlkem/cbmc.h */
#if defined(writeable)
#undef writeable
#endif

/* mlkem/compress.h */
#if defined(MLKEM_NATIVE_COMPRESS_H)
#undef MLKEM_NATIVE_COMPRESS_H
#endif

/* mlkem/compress.h */
#if defined(poly_compress_d10)
#undef poly_compress_d10
#endif

/* mlkem/compress.h */
#if defined(poly_compress_d11)
#undef poly_compress_d11
#endif

/* mlkem/compress.h */
#if defined(poly_compress_d4)
#undef poly_compress_d4
#endif

/* mlkem/compress.h */
#if defined(poly_compress_d5)
#undef poly_compress_d5
#endif

/* mlkem/compress.h */
#if defined(poly_decompress_d10)
#undef poly_decompress_d10
#endif

/* mlkem/compress.h */
#if defined(poly_decompress_d11)
#undef poly_decompress_d11
#endif

/* mlkem/compress.h */
#if defined(poly_decompress_d4)
#undef poly_decompress_d4
#endif

/* mlkem/compress.h */
#if defined(poly_decompress_d5)
#undef poly_decompress_d5
#endif

/* mlkem/compress.h */
#if defined(poly_frombytes)
#undef poly_frombytes
#endif

/* mlkem/compress.h */
#if defined(poly_frommsg)
#undef poly_frommsg
#endif

/* mlkem/compress.h */
#if defined(poly_tobytes)
#undef poly_tobytes
#endif

/* mlkem/compress.h */
#if defined(poly_tomsg)
#undef poly_tomsg
#endif

/* mlkem/compress.h */
#if defined(scalar_compress_d1)
#undef scalar_compress_d1
#endif

/* mlkem/compress.h */
#if defined(scalar_compress_d10)
#undef scalar_compress_d10
#endif

/* mlkem/compress.h */
#if defined(scalar_compress_d11)
#undef scalar_compress_d11
#endif

/* mlkem/compress.h */
#if defined(scalar_compress_d4)
#undef scalar_compress_d4
#endif

/* mlkem/compress.h */
#if defined(scalar_compress_d5)
#undef scalar_compress_d5
#endif

/* mlkem/compress.h */
#if defined(scalar_decompress_d10)
#undef scalar_decompress_d10
#endif

/* mlkem/compress.h */
#if defined(scalar_decompress_d11)
#undef scalar_decompress_d11
#endif

/* mlkem/compress.h */
#if defined(scalar_decompress_d4)
#undef scalar_decompress_d4
#endif

/* mlkem/compress.h */
#if defined(scalar_decompress_d5)
#undef scalar_decompress_d5
#endif

/* mlkem/debug.c */
#if defined(MLKEM_NATIVE_DEBUG_ERROR_HEADER)
#undef MLKEM_NATIVE_DEBUG_ERROR_HEADER
#endif

/* mlkem/debug.h */
#if defined(MLKEM_NATIVE_DEBUG_H)
#undef MLKEM_NATIVE_DEBUG_H
#endif

/* mlkem/debug.h */
#if defined(debug_assert)
#undef debug_assert
#endif

/* mlkem/debug.h */
#if defined(debug_assert_abs_bound)
#undef debug_assert_abs_bound
#endif

/* mlkem/debug.h */
#if defined(debug_assert_abs_bound_2d)
#undef debug_assert_abs_bound_2d
#endif

/* mlkem/debug.h */
#if defined(debug_assert_bound)
#undef debug_assert_bound
#endif

/* mlkem/debug.h */
#if defined(debug_assert_bound_2d)
#undef debug_assert_bound_2d
#endif

/* mlkem/debug.h */
#if defined(mlkem_debug_assert)
#undef mlkem_debug_assert
#endif

/* mlkem/debug.h */
#if defined(mlkem_debug_check_bounds)
#undef mlkem_debug_check_bounds
#endif

/* mlkem/fips202/fips202.c */
#if defined(keccak_absorb_once)
#undef keccak_absorb_once
#endif

/* mlkem/fips202/fips202.c */
#if defined(keccak_squeeze_once)
#undef keccak_squeeze_once
#endif

/* mlkem/fips202/fips202.c */
#if defined(keccak_squeezeblocks)
#undef keccak_squeezeblocks
#endif

/* mlkem/fips202/fips202.c */
#if defined(shake256ctx)
#undef shake256ctx
#endif

/* mlkem/fips202/fips202.h */
#if defined(FIPS202_X4_DEFAULT_IMPLEMENTATION)
#undef FIPS202_X4_DEFAULT_IMPLEMENTATION
#endif

/* mlkem/fips202/fips202.h */
#if defined(MLKEM_NATIVE_FIPS202_FIPS202_H)
#undef MLKEM_NATIVE_FIPS202_FIPS202_H
#endif

/* mlkem/fips202/fips202.h */
#if defined(SHA3_256_HASHBYTES)
#undef SHA3_256_HASHBYTES
#endif

/* mlkem/fips202/fips202.h */
#if defined(SHA3_256_RATE)
#undef SHA3_256_RATE
#endif

/* mlkem/fips202/fips202.h */
#if defined(SHA3_384_RATE)
#undef SHA3_384_RATE
#endif

/* mlkem/fips202/fips202.h */
#if defined(SHA3_512_HASHBYTES)
#undef SHA3_512_HASHBYTES
#endif

/* mlkem/fips202/fips202.h */
#if defined(SHA3_512_RATE)
#undef SHA3_512_RATE
#endif

/* mlkem/fips202/fips202.h */
#if defined(SHAKE128_RATE)
#undef SHAKE128_RATE
#endif

/* mlkem/fips202/fips202.h */
#if defined(SHAKE256_RATE)
#undef SHAKE256_RATE
#endif

/* mlkem/fips202/fips202.h */
#if defined(sha3_256)
#undef sha3_256
#endif

/* mlkem/fips202/fips202.h */
#if defined(sha3_512)
#undef sha3_512
#endif

/* mlkem/fips202/fips202.h */
#if defined(shake128_absorb_once)
#undef shake128_absorb_once
#endif

/* mlkem/fips202/fips202.h */
#if defined(shake128_init)
#undef shake128_init
#endif

/* mlkem/fips202/fips202.h */
#if defined(shake128_release)
#undef shake128_release
#endif

/* mlkem/fips202/fips202.h */
#if defined(shake128_squeezeblocks)
#undef shake128_squeezeblocks
#endif

/* mlkem/fips202/fips202.h */
#if defined(shake128ctx)
#undef shake128ctx
#endif

/* mlkem/fips202/fips202.h */
#if defined(shake256)
#undef shake256
#endif

/* mlkem/fips202/fips202_backend.h */
#if defined(MLKEM_NATIVE_FIPS202_FIPS202_BACKEND_H)
#undef MLKEM_NATIVE_FIPS202_FIPS202_BACKEND_H
#endif

/* mlkem/fips202/fips202x4.c */
#if defined(keccak_absorb_once_x4)
#undef keccak_absorb_once_x4
#endif

/* mlkem/fips202/fips202x4.c */
#if defined(keccak_squeezeblocks_x4)
#undef keccak_squeezeblocks_x4
#endif

/* mlkem/fips202/fips202x4.c */
#if defined(shake256x4_absorb_once)
#undef shake256x4_absorb_once
#endif

/* mlkem/fips202/fips202x4.c */
#if defined(shake256x4_ctx)
#undef shake256x4_ctx
#endif

/* mlkem/fips202/fips202x4.c */
#if defined(shake256x4_squeezeblocks)
#undef shake256x4_squeezeblocks
#endif

/* mlkem/fips202/fips202x4.h */
#if defined(MLKEM_NATIVE_FIPS202_FIPS202X4_H)
#undef MLKEM_NATIVE_FIPS202_FIPS202X4_H
#endif

/* mlkem/fips202/fips202x4.h */
#if defined(shake128x4_absorb_once)
#undef shake128x4_absorb_once
#endif

/* mlkem/fips202/fips202x4.h */
#if defined(shake128x4_init)
#undef shake128x4_init
#endif

/* mlkem/fips202/fips202x4.h */
#if defined(shake128x4_release)
#undef shake128x4_release
#endif

/* mlkem/fips202/fips202x4.h */
#if defined(shake128x4_squeezeblocks)
#undef shake128x4_squeezeblocks
#endif

/* mlkem/fips202/fips202x4.h */
#if defined(shake128x4ctx)
#undef shake128x4ctx
#endif

/* mlkem/fips202/fips202x4.h */
#if defined(shake256x4)
#undef shake256x4
#endif

/* mlkem/fips202/keccakf1600.c */
#if defined(KeccakF_RoundConstants)
#undef KeccakF_RoundConstants
#endif

/* mlkem/fips202/keccakf1600.c */
#if defined(NROUNDS)
#undef NROUNDS
#endif

/* mlkem/fips202/keccakf1600.c */
#if defined(ROL)
#undef ROL
#endif

/* mlkem/fips202/keccakf1600.h */
#if defined(KECCAK_LANES)
#undef KECCAK_LANES
#endif

/* mlkem/fips202/keccakf1600.h */
#if defined(KeccakF1600_StateExtractBytes)
#undef KeccakF1600_StateExtractBytes
#endif

/* mlkem/fips202/keccakf1600.h */
#if defined(KeccakF1600_StatePermute)
#undef KeccakF1600_StatePermute
#endif

/* mlkem/fips202/keccakf1600.h */
#if defined(KeccakF1600_StateXORBytes)
#undef KeccakF1600_StateXORBytes
#endif

/* mlkem/fips202/keccakf1600.h */
#if defined(KeccakF1600x4_StateExtractBytes)
#undef KeccakF1600x4_StateExtractBytes
#endif

/* mlkem/fips202/keccakf1600.h */
#if defined(KeccakF1600x4_StatePermute)
#undef KeccakF1600x4_StatePermute
#endif

/* mlkem/fips202/keccakf1600.h */
#if defined(KeccakF1600x4_StateXORBytes)
#undef KeccakF1600x4_StateXORBytes
#endif

/* mlkem/fips202/keccakf1600.h */
#if defined(MLKEM_NATIVE_FIPS202_KECCAKF1600_H)
#undef MLKEM_NATIVE_FIPS202_KECCAKF1600_H
#endif

/* mlkem/poly.c */
#if defined(barrett_reduce)
#undef barrett_reduce
#endif

/* mlkem/poly.c */
#if defined(fqmul)
#undef fqmul
#endif

/* mlkem/poly.c */
#if defined(invntt_layer)
#undef invntt_layer
#endif

/* mlkem/poly.c */
#if defined(ntt_butterfly_block)
#undef ntt_butterfly_block
#endif

/* mlkem/poly.c */
#if defined(ntt_layer)
#undef ntt_layer
#endif

/* mlkem/poly.c */
#if defined(scalar_signed_to_unsigned_q)
#undef scalar_signed_to_unsigned_q
#endif

/* mlkem/poly.h */
#if defined(INVNTT_BOUND)
#undef INVNTT_BOUND
#endif

/* mlkem/poly.h */
#if defined(MLKEM_NATIVE_POLY_H)
#undef MLKEM_NATIVE_POLY_H
#endif

/* mlkem/poly.h */
#if defined(NTT_BOUND)
#undef NTT_BOUND
#endif

/* mlkem/poly.h */
#if defined(cast_uint16_to_int16)
#undef cast_uint16_to_int16
#endif

/* mlkem/poly.h */
#if defined(montgomery_reduce)
#undef montgomery_reduce
#endif

/* mlkem/poly.h */
#if defined(poly)
#undef poly
#endif

/* mlkem/poly.h */
#if defined(poly_add)
#undef poly_add
#endif

/* mlkem/poly.h */
#if defined(poly_invntt_tomont)
#undef poly_invntt_tomont
#endif

/* mlkem/poly.h */
#if defined(poly_mulcache)
#undef poly_mulcache
#endif

/* mlkem/poly.h */
#if defined(poly_mulcache_compute)
#undef poly_mulcache_compute
#endif

/* mlkem/poly.h */
#if defined(poly_ntt)
#undef poly_ntt
#endif

/* mlkem/poly.h */
#if defined(poly_reduce)
#undef poly_reduce
#endif

/* mlkem/poly.h */
#if defined(poly_sub)
#undef poly_sub
#endif

/* mlkem/poly.h */
#if defined(poly_tomont)
#undef poly_tomont
#endif

/* mlkem/poly.h */
#if defined(zetas)
#undef zetas
#endif

/* mlkem/randombytes.h */
#if defined(MLKEM_NATIVE_RANDOMBYTES_H)
#undef MLKEM_NATIVE_RANDOMBYTES_H
#endif

/* mlkem/sampling.c */
#if defined(MLKEM_GEN_MATRIX_NBLOCKS)
#undef MLKEM_GEN_MATRIX_NBLOCKS
#endif

/* mlkem/sampling.c */
#if defined(load24_littleendian)
#undef load24_littleendian
#endif

/* mlkem/sampling.c */
#if defined(load32_littleendian)
#undef load32_littleendian
#endif

/* mlkem/sampling.c */
#if defined(rej_uniform)
#undef rej_uniform
#endif

/* mlkem/sampling.c */
#if defined(rej_uniform_scalar)
#undef rej_uniform_scalar
#endif

/* mlkem/sampling.h */
#if defined(MLKEM_NATIVE_SAMPLING_H)
#undef MLKEM_NATIVE_SAMPLING_H
#endif

/* mlkem/sampling.h */
#if defined(poly_cbd2)
#undef poly_cbd2
#endif

/* mlkem/sampling.h */
#if defined(poly_cbd3)
#undef poly_cbd3
#endif

/* mlkem/sampling.h */
#if defined(poly_rej_uniform)
#undef poly_rej_uniform
#endif

/* mlkem/sampling.h */
#if defined(poly_rej_uniform_x4)
#undef poly_rej_uniform_x4
#endif

/* mlkem/symmetric.h */
#if defined(MLKEM_NATIVE_SYMMETRIC_H)
#undef MLKEM_NATIVE_SYMMETRIC_H
#endif

/* mlkem/symmetric.h */
#if defined(XOF_RATE)
#undef XOF_RATE
#endif

/* mlkem/symmetric.h */
#if defined(hash_g)
#undef hash_g
#endif

/* mlkem/symmetric.h */
#if defined(hash_h)
#undef hash_h
#endif

/* mlkem/symmetric.h */
#if defined(hash_j)
#undef hash_j
#endif

/* mlkem/symmetric.h */
#if defined(prf_eta)
#undef prf_eta
#endif

/* mlkem/symmetric.h */
#if defined(prf_eta1)
#undef prf_eta1
#endif

/* mlkem/symmetric.h */
#if defined(prf_eta1_x4)
#undef prf_eta1_x4
#endif

/* mlkem/symmetric.h */
#if defined(prf_eta2)
#undef prf_eta2
#endif

/* mlkem/symmetric.h */
#if defined(xof_absorb)
#undef xof_absorb
#endif

/* mlkem/symmetric.h */
#if defined(xof_ctx)
#undef xof_ctx
#endif

/* mlkem/symmetric.h */
#if defined(xof_init)
#undef xof_init
#endif

/* mlkem/symmetric.h */
#if defined(xof_release)
#undef xof_release
#endif

/* mlkem/symmetric.h */
#if defined(xof_squeezeblocks)
#undef xof_squeezeblocks
#endif

/* mlkem/symmetric.h */
#if defined(xof_x4_absorb)
#undef xof_x4_absorb
#endif

/* mlkem/symmetric.h */
#if defined(xof_x4_ctx)
#undef xof_x4_ctx
#endif

/* mlkem/symmetric.h */
#if defined(xof_x4_init)
#undef xof_x4_init
#endif

/* mlkem/symmetric.h */
#if defined(xof_x4_release)
#undef xof_x4_release
#endif

/* mlkem/symmetric.h */
#if defined(xof_x4_squeezeblocks)
#undef xof_x4_squeezeblocks
#endif

/* mlkem/sys.h */
#if defined(ALIGN)
#undef ALIGN
#endif

/* mlkem/sys.h */
#if defined(ALWAYS_INLINE)
#undef ALWAYS_INLINE
#endif

/* mlkem/sys.h */
#if defined(DEFAULT_ALIGN)
#undef DEFAULT_ALIGN
#endif

/* mlkem/sys.h */
#if defined(INLINE)
#undef INLINE
#endif

/* mlkem/sys.h */
#if defined(MLKEM_NATIVE_SYS_H)
#undef MLKEM_NATIVE_SYS_H
#endif

/* mlkem/sys.h */
#if defined(RESTRICT)
#undef RESTRICT
#endif

/* mlkem/sys.h */
#if defined(SYS_AARCH64)
#undef SYS_AARCH64
#endif

/* mlkem/sys.h */
#if defined(SYS_AARCH64_EB)
#undef SYS_AARCH64_EB
#endif

/* mlkem/sys.h */
#if defined(SYS_BIG_ENDIAN)
#undef SYS_BIG_ENDIAN
#endif

/* mlkem/sys.h */
#if defined(SYS_LITTLE_ENDIAN)
#undef SYS_LITTLE_ENDIAN
#endif

/* mlkem/sys.h */
#if defined(SYS_X86_64)
#undef SYS_X86_64
#endif

/* mlkem/sys.h */
#if defined(SYS_X86_64_AVX2)
#undef SYS_X86_64_AVX2
#endif

/* mlkem/sys.h */
#if defined(asm)
#undef asm
#endif

/* mlkem/verify.h */
#if defined(MLKEM_NATIVE_VERIFY_H)
#undef MLKEM_NATIVE_VERIFY_H
#endif

/* mlkem/verify.h */
#if defined(MLKEM_USE_ASM_VALUE_BARRIER)
#undef MLKEM_USE_ASM_VALUE_BARRIER
#endif

/* mlkem/verify.h */
#if defined(ct_cmask_neg_i16)
#undef ct_cmask_neg_i16
#endif

/* mlkem/verify.h */
#if defined(ct_cmask_nonzero_u16)
#undef ct_cmask_nonzero_u16
#endif

/* mlkem/verify.h */
#if defined(ct_cmask_nonzero_u8)
#undef ct_cmask_nonzero_u8
#endif

/* mlkem/verify.h */
#if defined(ct_cmov_zero)
#undef ct_cmov_zero
#endif

/* mlkem/verify.h */
#if defined(ct_memcmp)
#undef ct_memcmp
#endif

/* mlkem/verify.h */
#if defined(ct_opt_blocker_u64)
#undef ct_opt_blocker_u64
#endif

/* mlkem/verify.h */
#if defined(ct_sel_int16)
#undef ct_sel_int16
#endif

/* mlkem/verify.h */
#if defined(ct_sel_uint8)
#undef ct_sel_uint8
#endif

/* mlkem/verify.h */
#if defined(value_barrier_i32)
#undef value_barrier_i32
#endif

/* mlkem/verify.h */
#if defined(value_barrier_u32)
#undef value_barrier_u32
#endif

/* mlkem/verify.h */
#if defined(value_barrier_u8)
#undef value_barrier_u8
#endif

#if defined(MLKEM_NATIVE_MONOBUILD_WITH_NATIVE)

/*
 * Undo all #define directives from *.[ch] files (native code)
 */

/* mlkem/fips202/native/aarch64/cortex_a55.h */
#if defined(FIPS202_NATIVE_PROFILE_H)
#undef FIPS202_NATIVE_PROFILE_H
#endif

/* mlkem/fips202/native/aarch64/cortex_a55.h */
#if defined(MLKEM_NATIVE_FIPS202_BACKEND_AARCH64_A55)
#undef MLKEM_NATIVE_FIPS202_BACKEND_AARCH64_A55
#endif

/* mlkem/fips202/native/aarch64/cortex_a55.h */
#if defined(MLKEM_NATIVE_FIPS202_BACKEND_IMPL)
#undef MLKEM_NATIVE_FIPS202_BACKEND_IMPL
#endif

/* mlkem/fips202/native/aarch64/cortex_a55.h */
#if defined(MLKEM_NATIVE_FIPS202_BACKEND_NAME)
#undef MLKEM_NATIVE_FIPS202_BACKEND_NAME
#endif

/* mlkem/fips202/native/aarch64/cortex_a55.h */
#if defined(MLKEM_NATIVE_FIPS202_NATIVE_AARCH64_CORTEX_A55_H)
#undef MLKEM_NATIVE_FIPS202_NATIVE_AARCH64_CORTEX_A55_H
#endif

/* mlkem/fips202/native/aarch64/default.h */
#if defined(FIPS202_NATIVE_PROFILE_H)
#undef FIPS202_NATIVE_PROFILE_H
#endif

/* mlkem/fips202/native/aarch64/default.h */
#if defined(MLKEM_NATIVE_FIPS202_BACKEND_AARCH64_DEFAULT)
#undef MLKEM_NATIVE_FIPS202_BACKEND_AARCH64_DEFAULT
#endif

/* mlkem/fips202/native/aarch64/default.h */
#if defined(MLKEM_NATIVE_FIPS202_BACKEND_IMPL)
#undef MLKEM_NATIVE_FIPS202_BACKEND_IMPL
#endif

/* mlkem/fips202/native/aarch64/default.h */
#if defined(MLKEM_NATIVE_FIPS202_BACKEND_NAME)
#undef MLKEM_NATIVE_FIPS202_BACKEND_NAME
#endif

/* mlkem/fips202/native/aarch64/default.h */
#if defined(MLKEM_NATIVE_FIPS202_NATIVE_AARCH64_DEFAULT_H)
#undef MLKEM_NATIVE_FIPS202_NATIVE_AARCH64_DEFAULT_H
#endif

/* mlkem/fips202/native/aarch64/src/cortex_a55_impl.h */
#if defined(FIPS202_NATIVE_PROFILE_IMPL_H)
#undef FIPS202_NATIVE_PROFILE_IMPL_H
#endif

/* mlkem/fips202/native/aarch64/src/cortex_a55_impl.h */
#if defined(MLKEM_NATIVE_FIPS202_NATIVE_AARCH64_SRC_CORTEX_A55_IMPL_H)
#undef MLKEM_NATIVE_FIPS202_NATIVE_AARCH64_SRC_CORTEX_A55_IMPL_H
#endif

/* mlkem/fips202/native/aarch64/src/cortex_a55_impl.h */
#if defined(MLKEM_USE_FIPS202_X1_NATIVE)
#undef MLKEM_USE_FIPS202_X1_NATIVE
#endif

/* mlkem/fips202/native/aarch64/src/default_impl.h */
#if defined(FIPS202_NATIVE_PROFILE_IMPL_H)
#undef FIPS202_NATIVE_PROFILE_IMPL_H
#endif

/* mlkem/fips202/native/aarch64/src/default_impl.h */
#if defined(MLKEM_NATIVE_FIPS202_NATIVE_AARCH64_SRC_DEFAULT_IMPL_H)
#undef MLKEM_NATIVE_FIPS202_NATIVE_AARCH64_SRC_DEFAULT_IMPL_H
#endif

/* mlkem/fips202/native/aarch64/src/default_impl.h */
#if defined(MLKEM_USE_FIPS202_X1_NATIVE)
#undef MLKEM_USE_FIPS202_X1_NATIVE
#endif

/* mlkem/fips202/native/aarch64/src/default_impl.h */
#if defined(MLKEM_USE_FIPS202_X2_NATIVE)
#undef MLKEM_USE_FIPS202_X2_NATIVE
#endif

/* mlkem/fips202/native/aarch64/src/default_impl.h */
#if defined(MLKEM_USE_FIPS202_X4_NATIVE)
#undef MLKEM_USE_FIPS202_X4_NATIVE
#endif

/* mlkem/fips202/native/aarch64/src/fips202_native_aarch64.h */
#if defined(MLKEM_NATIVE_FIPS202_NATIVE_AARCH64_SRC_FIPS202_NATIVE_AARCH64_H)
#undef MLKEM_NATIVE_FIPS202_NATIVE_AARCH64_SRC_FIPS202_NATIVE_AARCH64_H
#endif

/* mlkem/fips202/native/aarch64/src/fips202_native_aarch64.h */
#if defined(keccak_f1600_x1_scalar_asm_opt)
#undef keccak_f1600_x1_scalar_asm_opt
#endif

/* mlkem/fips202/native/aarch64/src/fips202_native_aarch64.h */
#if defined(keccak_f1600_x1_v84a_asm_clean)
#undef keccak_f1600_x1_v84a_asm_clean
#endif

/* mlkem/fips202/native/aarch64/src/fips202_native_aarch64.h */
#if defined(keccak_f1600_x2_v84a_asm_clean)
#undef keccak_f1600_x2_v84a_asm_clean
#endif

/* mlkem/fips202/native/aarch64/src/fips202_native_aarch64.h */
#if defined(keccak_f1600_x2_v8a_v84a_asm_hybrid)
#undef keccak_f1600_x2_v8a_v84a_asm_hybrid
#endif

/* mlkem/fips202/native/aarch64/src/fips202_native_aarch64.h */
#if defined(keccak_f1600_x4_scalar_v84a_asm_hybrid_opt)
#undef keccak_f1600_x4_scalar_v84a_asm_hybrid_opt
#endif

/* mlkem/fips202/native/aarch64/src/fips202_native_aarch64.h */
#if defined(keccak_f1600_x4_scalar_v8a_asm_hybrid_opt)
#undef keccak_f1600_x4_scalar_v8a_asm_hybrid_opt
#endif

/* mlkem/fips202/native/aarch64/src/fips202_native_aarch64.h */
#if defined(keccak_f1600_x4_scalar_v8a_v84a_hybrid_asm_opt)
#undef keccak_f1600_x4_scalar_v8a_v84a_hybrid_asm_opt
#endif

/* mlkem/fips202/native/aarch64/src/fips202_native_aarch64.h */
#if defined(keccakf1600_round_constants)
#undef keccakf1600_round_constants
#endif

/* mlkem/fips202/native/api.h */
#if defined(MLKEM_NATIVE_FIPS202_NATIVE_API_H)
#undef MLKEM_NATIVE_FIPS202_NATIVE_API_H
#endif

/* mlkem/fips202/native/default.h */
#if defined(MLKEM_NATIVE_FIPS202_NATIVE_DEFAULT_H)
#undef MLKEM_NATIVE_FIPS202_NATIVE_DEFAULT_H
#endif

/* mlkem/fips202/native/x86_64/src/KeccakP-1600-times4-SIMD256.c */
#if defined(ANDnu256)
#undef ANDnu256
#endif

/* mlkem/fips202/native/x86_64/src/KeccakP-1600-times4-SIMD256.c */
#if defined(CONST256)
#undef CONST256
#endif

/* mlkem/fips202/native/x86_64/src/KeccakP-1600-times4-SIMD256.c */
#if defined(CONST256_64)
#undef CONST256_64
#endif

/* mlkem/fips202/native/x86_64/src/KeccakP-1600-times4-SIMD256.c */
#if defined(ROL64in256)
#undef ROL64in256
#endif

/* mlkem/fips202/native/x86_64/src/KeccakP-1600-times4-SIMD256.c */
#if defined(ROL64in256_56)
#undef ROL64in256_56
#endif

/* mlkem/fips202/native/x86_64/src/KeccakP-1600-times4-SIMD256.c */
#if defined(ROL64in256_8)
#undef ROL64in256_8
#endif

/* mlkem/fips202/native/x86_64/src/KeccakP-1600-times4-SIMD256.c */
#if defined(SCATTER_STORE256)
#undef SCATTER_STORE256
#endif

/* mlkem/fips202/native/x86_64/src/KeccakP-1600-times4-SIMD256.c */
#if defined(STORE256)
#undef STORE256
#endif

/* mlkem/fips202/native/x86_64/src/KeccakP-1600-times4-SIMD256.c */
#if defined(SnP_laneLengthInBytes)
#undef SnP_laneLengthInBytes
#endif

/* mlkem/fips202/native/x86_64/src/KeccakP-1600-times4-SIMD256.c */
#if defined(XOR256)
#undef XOR256
#endif

/* mlkem/fips202/native/x86_64/src/KeccakP-1600-times4-SIMD256.c */
#if defined(XOReq256)
#undef XOReq256
#endif

/* mlkem/fips202/native/x86_64/src/KeccakP-1600-times4-SIMD256.c */
#if defined(copyFromState)
#undef copyFromState
#endif

/* mlkem/fips202/native/x86_64/src/KeccakP-1600-times4-SIMD256.c */
#if defined(copyStateVariables)
#undef copyStateVariables
#endif

/* mlkem/fips202/native/x86_64/src/KeccakP-1600-times4-SIMD256.c */
#if defined(copyToState)
#undef copyToState
#endif

/* mlkem/fips202/native/x86_64/src/KeccakP-1600-times4-SIMD256.c */
#if defined(declareABCDE)
#undef declareABCDE
#endif

/* mlkem/fips202/native/x86_64/src/KeccakP-1600-times4-SIMD256.c */
#if defined(prepareTheta)
#undef prepareTheta
#endif

/* mlkem/fips202/native/x86_64/src/KeccakP-1600-times4-SIMD256.c */
#if defined(rounds24)
#undef rounds24
#endif

/* mlkem/fips202/native/x86_64/src/KeccakP-1600-times4-SIMD256.c */
#if defined(thetaRhoPiChiIota)
#undef thetaRhoPiChiIota
#endif

/* mlkem/fips202/native/x86_64/src/KeccakP-1600-times4-SIMD256.c */
#if defined(thetaRhoPiChiIotaPrepareTheta)
#undef thetaRhoPiChiIotaPrepareTheta
#endif

/* mlkem/fips202/native/x86_64/src/xkcp_impl.h */
#if defined(KeccakP1600times4_PermuteAll_24rounds)
#undef KeccakP1600times4_PermuteAll_24rounds
#endif

/* mlkem/fips202/native/x86_64/src/xkcp_impl.h */
#if defined(MLKEM_NATIVE_FIPS202_NATIVE_X86_64_SRC_XKCP_IMPL_H)
#undef MLKEM_NATIVE_FIPS202_NATIVE_X86_64_SRC_XKCP_IMPL_H
#endif

/* mlkem/fips202/native/x86_64/src/xkcp_impl.h */
#if defined(MLKEM_NATIVE_FIPS202_PROFILE_IMPL_H)
#undef MLKEM_NATIVE_FIPS202_PROFILE_IMPL_H
#endif

/* mlkem/fips202/native/x86_64/src/xkcp_impl.h */
#if defined(MLKEM_USE_FIPS202_X4_NATIVE)
#undef MLKEM_USE_FIPS202_X4_NATIVE
#endif

/* mlkem/fips202/native/x86_64/xkcp.h */
#if defined(MLKEM_NATIVE_FIPS202_BACKEND_IMPL)
#undef MLKEM_NATIVE_FIPS202_BACKEND_IMPL
#endif

/* mlkem/fips202/native/x86_64/xkcp.h */
#if defined(MLKEM_NATIVE_FIPS202_BACKEND_NAME)
#undef MLKEM_NATIVE_FIPS202_BACKEND_NAME
#endif

/* mlkem/fips202/native/x86_64/xkcp.h */
#if defined(MLKEM_NATIVE_FIPS202_BACKEND_X86_64_XKCP)
#undef MLKEM_NATIVE_FIPS202_BACKEND_X86_64_XKCP
#endif

/* mlkem/fips202/native/x86_64/xkcp.h */
#if defined(MLKEM_NATIVE_FIPS202_NATIVE_X86_64_XKCP_H)
#undef MLKEM_NATIVE_FIPS202_NATIVE_X86_64_XKCP_H
#endif

/* mlkem/fips202/native/x86_64/xkcp.h */
#if defined(MLKEM_NATIVE_FIPS202_PROFILE_H)
#undef MLKEM_NATIVE_FIPS202_PROFILE_H
#endif

/* mlkem/native/aarch64/opt.h */
#if defined(MLKEM_NATIVE_ARITH_BACKEND_AARCH64_OPT)
#undef MLKEM_NATIVE_ARITH_BACKEND_AARCH64_OPT
#endif

/* mlkem/native/aarch64/opt.h */
#if defined(MLKEM_NATIVE_ARITH_BACKEND_IMPL)
#undef MLKEM_NATIVE_ARITH_BACKEND_IMPL
#endif

/* mlkem/native/aarch64/opt.h */
#if defined(MLKEM_NATIVE_ARITH_BACKEND_NAME)
#undef MLKEM_NATIVE_ARITH_BACKEND_NAME
#endif

/* mlkem/native/aarch64/opt.h */
#if defined(MLKEM_NATIVE_ARITH_PROFILE_H)
#undef MLKEM_NATIVE_ARITH_PROFILE_H
#endif

/* mlkem/native/aarch64/opt.h */
#if defined(MLKEM_NATIVE_NATIVE_AARCH64_OPT_H)
#undef MLKEM_NATIVE_NATIVE_AARCH64_OPT_H
#endif

/* mlkem/native/aarch64/src/arith_native_aarch64.h */
#if defined(MLKEM_NATIVE_NATIVE_AARCH64_SRC_ARITH_NATIVE_AARCH64_H)
#undef MLKEM_NATIVE_NATIVE_AARCH64_SRC_ARITH_NATIVE_AARCH64_H
#endif

/* mlkem/native/aarch64/src/arith_native_aarch64.h */
#if defined(aarch64_invntt_zetas_layer01234)
#undef aarch64_invntt_zetas_layer01234
#endif

/* mlkem/native/aarch64/src/arith_native_aarch64.h */
#if defined(aarch64_invntt_zetas_layer56)
#undef aarch64_invntt_zetas_layer56
#endif

/* mlkem/native/aarch64/src/arith_native_aarch64.h */
#if defined(aarch64_ntt_zetas_layer01234)
#undef aarch64_ntt_zetas_layer01234
#endif

/* mlkem/native/aarch64/src/arith_native_aarch64.h */
#if defined(aarch64_ntt_zetas_layer56)
#undef aarch64_ntt_zetas_layer56
#endif

/* mlkem/native/aarch64/src/arith_native_aarch64.h */
#if defined(aarch64_zetas_mulcache_native)
#undef aarch64_zetas_mulcache_native
#endif

/* mlkem/native/aarch64/src/arith_native_aarch64.h */
#if defined(aarch64_zetas_mulcache_twisted_native)
#undef aarch64_zetas_mulcache_twisted_native
#endif

/* mlkem/native/aarch64/src/arith_native_aarch64.h */
#if defined(intt_asm_opt)
#undef intt_asm_opt
#endif

/* mlkem/native/aarch64/src/arith_native_aarch64.h */
#if defined(ntt_asm_opt)
#undef ntt_asm_opt
#endif

/* mlkem/native/aarch64/src/arith_native_aarch64.h */
#if defined(poly_mulcache_compute_asm_opt)
#undef poly_mulcache_compute_asm_opt
#endif

/* mlkem/native/aarch64/src/arith_native_aarch64.h */
#if defined(poly_reduce_asm_opt)
#undef poly_reduce_asm_opt
#endif

/* mlkem/native/aarch64/src/arith_native_aarch64.h */
#if defined(poly_tobytes_asm_opt)
#undef poly_tobytes_asm_opt
#endif

/* mlkem/native/aarch64/src/arith_native_aarch64.h */
#if defined(poly_tomont_asm_opt)
#undef poly_tomont_asm_opt
#endif

/* mlkem/native/aarch64/src/arith_native_aarch64.h */
#if defined(polyvec_basemul_acc_montgomery_cached_asm_k2_opt)
#undef polyvec_basemul_acc_montgomery_cached_asm_k2_opt
#endif

/* mlkem/native/aarch64/src/arith_native_aarch64.h */
#if defined(polyvec_basemul_acc_montgomery_cached_asm_k3_opt)
#undef polyvec_basemul_acc_montgomery_cached_asm_k3_opt
#endif

/* mlkem/native/aarch64/src/arith_native_aarch64.h */
#if defined(polyvec_basemul_acc_montgomery_cached_asm_k4_opt)
#undef polyvec_basemul_acc_montgomery_cached_asm_k4_opt
#endif

/* mlkem/native/aarch64/src/arith_native_aarch64.h */
#if defined(rej_uniform_asm_clean)
#undef rej_uniform_asm_clean
#endif

/* mlkem/native/aarch64/src/arith_native_aarch64.h */
#if defined(rej_uniform_table)
#undef rej_uniform_table
#endif

/* mlkem/native/aarch64/src/consts.h */
#if defined(MLKEM_NATIVE_NATIVE_AARCH64_SRC_CONSTS_H)
#undef MLKEM_NATIVE_NATIVE_AARCH64_SRC_CONSTS_H
#endif

/* mlkem/native/aarch64/src/consts.h */
#if defined(zetas_mulcache_native)
#undef zetas_mulcache_native
#endif

/* mlkem/native/aarch64/src/consts.h */
#if defined(zetas_mulcache_twisted_native)
#undef zetas_mulcache_twisted_native
#endif

/* mlkem/native/aarch64/src/opt_impl.h */
#if defined(MLKEM_NATIVE_ARITH_PROFILE_IMPL_H)
#undef MLKEM_NATIVE_ARITH_PROFILE_IMPL_H
#endif

/* mlkem/native/aarch64/src/opt_impl.h */
#if defined(MLKEM_NATIVE_NATIVE_AARCH64_SRC_OPT_IMPL_H)
#undef MLKEM_NATIVE_NATIVE_AARCH64_SRC_OPT_IMPL_H
#endif

/* mlkem/native/aarch64/src/opt_impl.h */
#if defined(MLKEM_USE_NATIVE_INTT)
#undef MLKEM_USE_NATIVE_INTT
#endif

/* mlkem/native/aarch64/src/opt_impl.h */
#if defined(MLKEM_USE_NATIVE_NTT)
#undef MLKEM_USE_NATIVE_NTT
#endif

/* mlkem/native/aarch64/src/opt_impl.h */
#if defined(MLKEM_USE_NATIVE_POLYVEC_BASEMUL_ACC_MONTGOMERY_CACHED)
#undef MLKEM_USE_NATIVE_POLYVEC_BASEMUL_ACC_MONTGOMERY_CACHED
#endif

/* mlkem/native/aarch64/src/opt_impl.h */
#if defined(MLKEM_USE_NATIVE_POLY_MULCACHE_COMPUTE)
#undef MLKEM_USE_NATIVE_POLY_MULCACHE_COMPUTE
#endif

/* mlkem/native/aarch64/src/opt_impl.h */
#if defined(MLKEM_USE_NATIVE_POLY_REDUCE)
#undef MLKEM_USE_NATIVE_POLY_REDUCE
#endif

/* mlkem/native/aarch64/src/opt_impl.h */
#if defined(MLKEM_USE_NATIVE_POLY_TOBYTES)
#undef MLKEM_USE_NATIVE_POLY_TOBYTES
#endif

/* mlkem/native/aarch64/src/opt_impl.h */
#if defined(MLKEM_USE_NATIVE_POLY_TOMONT)
#undef MLKEM_USE_NATIVE_POLY_TOMONT
#endif

/* mlkem/native/aarch64/src/opt_impl.h */
#if defined(MLKEM_USE_NATIVE_REJ_UNIFORM)
#undef MLKEM_USE_NATIVE_REJ_UNIFORM
#endif

/* mlkem/native/api.h */
#if defined(INVNTT_BOUND)
#undef INVNTT_BOUND
#endif

/* mlkem/native/api.h */
#if defined(MLKEM_NATIVE_NATIVE_API_H)
#undef MLKEM_NATIVE_NATIVE_API_H
#endif

/* mlkem/native/api.h */
#if defined(NTT_BOUND)
#undef NTT_BOUND
#endif

/* mlkem/native/default.h */
#if defined(MLKEM_NATIVE_NATIVE_DEFAULT_H)
#undef MLKEM_NATIVE_NATIVE_DEFAULT_H
#endif

/* mlkem/native/x86_64/default.h */
#if defined(MLKEM_NATIVE_ARITH_BACKEND_IMPL)
#undef MLKEM_NATIVE_ARITH_BACKEND_IMPL
#endif

/* mlkem/native/x86_64/default.h */
#if defined(MLKEM_NATIVE_ARITH_BACKEND_NAME)
#undef MLKEM_NATIVE_ARITH_BACKEND_NAME
#endif

/* mlkem/native/x86_64/default.h */
#if defined(MLKEM_NATIVE_ARITH_BACKEND_X86_64_DEFAULT)
#undef MLKEM_NATIVE_ARITH_BACKEND_X86_64_DEFAULT
#endif

/* mlkem/native/x86_64/default.h */
#if defined(MLKEM_NATIVE_ARITH_PROFILE_H)
#undef MLKEM_NATIVE_ARITH_PROFILE_H
#endif

/* mlkem/native/x86_64/default.h */
#if defined(MLKEM_NATIVE_NATIVE_X86_64_DEFAULT_H)
#undef MLKEM_NATIVE_NATIVE_X86_64_DEFAULT_H
#endif

/* mlkem/native/x86_64/src/align.h */
#if defined(ALIGNED_INT16)
#undef ALIGNED_INT16
#endif

/* mlkem/native/x86_64/src/align.h */
#if defined(ALIGNED_UINT8)
#undef ALIGNED_UINT8
#endif

/* mlkem/native/x86_64/src/align.h */
#if defined(ALIGN_H)
#undef ALIGN_H
#endif

/* mlkem/native/x86_64/src/align.h */
#if defined(MLKEM_NATIVE_NATIVE_X86_64_SRC_ALIGN_H)
#undef MLKEM_NATIVE_NATIVE_X86_64_SRC_ALIGN_H
#endif

/* mlkem/native/x86_64/src/arith_native_x86_64.h */
#if defined(MLKEM_NATIVE_NATIVE_X86_64_SRC_ARITH_NATIVE_X86_64_H)
#undef MLKEM_NATIVE_NATIVE_X86_64_SRC_ARITH_NATIVE_X86_64_H
#endif

/* mlkem/native/x86_64/src/arith_native_x86_64.h */
#if defined(REJ_UNIFORM_AVX_BUFLEN)
#undef REJ_UNIFORM_AVX_BUFLEN
#endif

/* mlkem/native/x86_64/src/arith_native_x86_64.h */
#if defined(REJ_UNIFORM_AVX_NBLOCKS)
#undef REJ_UNIFORM_AVX_NBLOCKS
#endif

/* mlkem/native/x86_64/src/arith_native_x86_64.h */
#if defined(basemul_avx2)
#undef basemul_avx2
#endif

/* mlkem/native/x86_64/src/arith_native_x86_64.h */
#if defined(invntt_avx2)
#undef invntt_avx2
#endif

/* mlkem/native/x86_64/src/arith_native_x86_64.h */
#if defined(ntt_avx2)
#undef ntt_avx2
#endif

/* mlkem/native/x86_64/src/arith_native_x86_64.h */
#if defined(nttfrombytes_avx2)
#undef nttfrombytes_avx2
#endif

/* mlkem/native/x86_64/src/arith_native_x86_64.h */
#if defined(nttpack_avx2)
#undef nttpack_avx2
#endif

/* mlkem/native/x86_64/src/arith_native_x86_64.h */
#if defined(ntttobytes_avx2)
#undef ntttobytes_avx2
#endif

/* mlkem/native/x86_64/src/arith_native_x86_64.h */
#if defined(nttunpack_avx2)
#undef nttunpack_avx2
#endif

/* mlkem/native/x86_64/src/arith_native_x86_64.h */
#if defined(poly_compress_d10_avx2)
#undef poly_compress_d10_avx2
#endif

/* mlkem/native/x86_64/src/arith_native_x86_64.h */
#if defined(poly_compress_d11_avx2)
#undef poly_compress_d11_avx2
#endif

/* mlkem/native/x86_64/src/arith_native_x86_64.h */
#if defined(poly_compress_d4_avx2)
#undef poly_compress_d4_avx2
#endif

/* mlkem/native/x86_64/src/arith_native_x86_64.h */
#if defined(poly_compress_d5_avx2)
#undef poly_compress_d5_avx2
#endif

/* mlkem/native/x86_64/src/arith_native_x86_64.h */
#if defined(poly_decompress_d10_avx2)
#undef poly_decompress_d10_avx2
#endif

/* mlkem/native/x86_64/src/arith_native_x86_64.h */
#if defined(poly_decompress_d11_avx2)
#undef poly_decompress_d11_avx2
#endif

/* mlkem/native/x86_64/src/arith_native_x86_64.h */
#if defined(poly_decompress_d4_avx2)
#undef poly_decompress_d4_avx2
#endif

/* mlkem/native/x86_64/src/arith_native_x86_64.h */
#if defined(poly_decompress_d5_avx2)
#undef poly_decompress_d5_avx2
#endif

/* mlkem/native/x86_64/src/arith_native_x86_64.h */
#if defined(polyvec_basemul_acc_montgomery_cached_avx2)
#undef polyvec_basemul_acc_montgomery_cached_avx2
#endif

/* mlkem/native/x86_64/src/arith_native_x86_64.h */
#if defined(reduce_avx2)
#undef reduce_avx2
#endif

/* mlkem/native/x86_64/src/arith_native_x86_64.h */
#if defined(rej_uniform_avx2)
#undef rej_uniform_avx2
#endif

/* mlkem/native/x86_64/src/arith_native_x86_64.h */
#if defined(rej_uniform_table)
#undef rej_uniform_table
#endif

/* mlkem/native/x86_64/src/arith_native_x86_64.h */
#if defined(tomont_avx2)
#undef tomont_avx2
#endif

/* mlkem/native/x86_64/src/consts.c */
#if defined(AVX2_BACKEND_DATA_OFFSET_16XFHI)
#undef AVX2_BACKEND_DATA_OFFSET_16XFHI
#endif

/* mlkem/native/x86_64/src/consts.c */
#if defined(AVX2_BACKEND_DATA_OFFSET_16XFLO)
#undef AVX2_BACKEND_DATA_OFFSET_16XFLO
#endif

/* mlkem/native/x86_64/src/consts.c */
#if defined(AVX2_BACKEND_DATA_OFFSET_16XMASK)
#undef AVX2_BACKEND_DATA_OFFSET_16XMASK
#endif

/* mlkem/native/x86_64/src/consts.c */
#if defined(AVX2_BACKEND_DATA_OFFSET_16XMONTSQHI)
#undef AVX2_BACKEND_DATA_OFFSET_16XMONTSQHI
#endif

/* mlkem/native/x86_64/src/consts.c */
#if defined(AVX2_BACKEND_DATA_OFFSET_16XMONTSQLO)
#undef AVX2_BACKEND_DATA_OFFSET_16XMONTSQLO
#endif

/* mlkem/native/x86_64/src/consts.c */
#if defined(AVX2_BACKEND_DATA_OFFSET_16XQ)
#undef AVX2_BACKEND_DATA_OFFSET_16XQ
#endif

/* mlkem/native/x86_64/src/consts.c */
#if defined(AVX2_BACKEND_DATA_OFFSET_16XQINV)
#undef AVX2_BACKEND_DATA_OFFSET_16XQINV
#endif

/* mlkem/native/x86_64/src/consts.c */
#if defined(AVX2_BACKEND_DATA_OFFSET_16XSHIFT)
#undef AVX2_BACKEND_DATA_OFFSET_16XSHIFT
#endif

/* mlkem/native/x86_64/src/consts.c */
#if defined(AVX2_BACKEND_DATA_OFFSET_16XV)
#undef AVX2_BACKEND_DATA_OFFSET_16XV
#endif

/* mlkem/native/x86_64/src/consts.c */
#if defined(AVX2_BACKEND_DATA_OFFSET_REVIDXB)
#undef AVX2_BACKEND_DATA_OFFSET_REVIDXB
#endif

/* mlkem/native/x86_64/src/consts.c */
#if defined(AVX2_BACKEND_DATA_OFFSET_REVIDXD)
#undef AVX2_BACKEND_DATA_OFFSET_REVIDXD
#endif

/* mlkem/native/x86_64/src/consts.c */
#if defined(AVX2_BACKEND_DATA_OFFSET_ZETAS_EXP)
#undef AVX2_BACKEND_DATA_OFFSET_ZETAS_EXP
#endif

/* mlkem/native/x86_64/src/consts.c */
#if defined(FHI)
#undef FHI
#endif

/* mlkem/native/x86_64/src/consts.c */
#if defined(FLO)
#undef FLO
#endif

/* mlkem/native/x86_64/src/consts.c */
#if defined(MASK)
#undef MASK
#endif

/* mlkem/native/x86_64/src/consts.c */
#if defined(MONT)
#undef MONT
#endif

/* mlkem/native/x86_64/src/consts.c */
#if defined(MONTSQHI)
#undef MONTSQHI
#endif

/* mlkem/native/x86_64/src/consts.c */
#if defined(MONTSQLO)
#undef MONTSQLO
#endif

/* mlkem/native/x86_64/src/consts.c */
#if defined(Q)
#undef Q
#endif

/* mlkem/native/x86_64/src/consts.c */
#if defined(QINV)
#undef QINV
#endif

/* mlkem/native/x86_64/src/consts.c */
#if defined(SHIFT)
#undef SHIFT
#endif

/* mlkem/native/x86_64/src/consts.c */
#if defined(V)
#undef V
#endif

/* mlkem/native/x86_64/src/consts.h */
#if defined(AVX2_BACKEND_DATA_OFFSET_16XFHI)
#undef AVX2_BACKEND_DATA_OFFSET_16XFHI
#endif

/* mlkem/native/x86_64/src/consts.h */
#if defined(AVX2_BACKEND_DATA_OFFSET_16XFLO)
#undef AVX2_BACKEND_DATA_OFFSET_16XFLO
#endif

/* mlkem/native/x86_64/src/consts.h */
#if defined(AVX2_BACKEND_DATA_OFFSET_16XMASK)
#undef AVX2_BACKEND_DATA_OFFSET_16XMASK
#endif

/* mlkem/native/x86_64/src/consts.h */
#if defined(AVX2_BACKEND_DATA_OFFSET_16XMONTSQHI)
#undef AVX2_BACKEND_DATA_OFFSET_16XMONTSQHI
#endif

/* mlkem/native/x86_64/src/consts.h */
#if defined(AVX2_BACKEND_DATA_OFFSET_16XMONTSQLO)
#undef AVX2_BACKEND_DATA_OFFSET_16XMONTSQLO
#endif

/* mlkem/native/x86_64/src/consts.h */
#if defined(AVX2_BACKEND_DATA_OFFSET_16XQ)
#undef AVX2_BACKEND_DATA_OFFSET_16XQ
#endif

/* mlkem/native/x86_64/src/consts.h */
#if defined(AVX2_BACKEND_DATA_OFFSET_16XQINV)
#undef AVX2_BACKEND_DATA_OFFSET_16XQINV
#endif

/* mlkem/native/x86_64/src/consts.h */
#if defined(AVX2_BACKEND_DATA_OFFSET_16XSHIFT)
#undef AVX2_BACKEND_DATA_OFFSET_16XSHIFT
#endif

/* mlkem/native/x86_64/src/consts.h */
#if defined(AVX2_BACKEND_DATA_OFFSET_16XV)
#undef AVX2_BACKEND_DATA_OFFSET_16XV
#endif

/* mlkem/native/x86_64/src/consts.h */
#if defined(AVX2_BACKEND_DATA_OFFSET_REVIDXB)
#undef AVX2_BACKEND_DATA_OFFSET_REVIDXB
#endif

/* mlkem/native/x86_64/src/consts.h */
#if defined(AVX2_BACKEND_DATA_OFFSET_REVIDXD)
#undef AVX2_BACKEND_DATA_OFFSET_REVIDXD
#endif

/* mlkem/native/x86_64/src/consts.h */
#if defined(AVX2_BACKEND_DATA_OFFSET_ZETAS_EXP)
#undef AVX2_BACKEND_DATA_OFFSET_ZETAS_EXP
#endif

/* mlkem/native/x86_64/src/consts.h */
#if defined(CONSTS_H)
#undef CONSTS_H
#endif

/* mlkem/native/x86_64/src/consts.h */
#if defined(MLKEM_NATIVE_NATIVE_X86_64_SRC_CONSTS_H)
#undef MLKEM_NATIVE_NATIVE_X86_64_SRC_CONSTS_H
#endif

/* mlkem/native/x86_64/src/consts.h */
#if defined(qdata)
#undef qdata
#endif

/* mlkem/native/x86_64/src/default_impl.h */
#if defined(MLKEM_NATIVE_ARITH_PROFILE_IMPL_H)
#undef MLKEM_NATIVE_ARITH_PROFILE_IMPL_H
#endif

/* mlkem/native/x86_64/src/default_impl.h */
#if defined(MLKEM_NATIVE_NATIVE_X86_64_SRC_DEFAULT_IMPL_H)
#undef MLKEM_NATIVE_NATIVE_X86_64_SRC_DEFAULT_IMPL_H
#endif

/* mlkem/native/x86_64/src/default_impl.h */
#if defined(MLKEM_USE_NATIVE_INTT)
#undef MLKEM_USE_NATIVE_INTT
#endif

/* mlkem/native/x86_64/src/default_impl.h */
#if defined(MLKEM_USE_NATIVE_NTT)
#undef MLKEM_USE_NATIVE_NTT
#endif

/* mlkem/native/x86_64/src/default_impl.h */
#if defined(MLKEM_USE_NATIVE_NTT_CUSTOM_ORDER)
#undef MLKEM_USE_NATIVE_NTT_CUSTOM_ORDER
#endif

/* mlkem/native/x86_64/src/default_impl.h */
#if defined(MLKEM_USE_NATIVE_POLYVEC_BASEMUL_ACC_MONTGOMERY_CACHED)
#undef MLKEM_USE_NATIVE_POLYVEC_BASEMUL_ACC_MONTGOMERY_CACHED
#endif

/* mlkem/native/x86_64/src/default_impl.h */
#if defined(MLKEM_USE_NATIVE_POLY_COMPRESS_D10)
#undef MLKEM_USE_NATIVE_POLY_COMPRESS_D10
#endif

/* mlkem/native/x86_64/src/default_impl.h */
#if defined(MLKEM_USE_NATIVE_POLY_COMPRESS_D11)
#undef MLKEM_USE_NATIVE_POLY_COMPRESS_D11
#endif

/* mlkem/native/x86_64/src/default_impl.h */
#if defined(MLKEM_USE_NATIVE_POLY_COMPRESS_D4)
#undef MLKEM_USE_NATIVE_POLY_COMPRESS_D4
#endif

/* mlkem/native/x86_64/src/default_impl.h */
#if defined(MLKEM_USE_NATIVE_POLY_COMPRESS_D5)
#undef MLKEM_USE_NATIVE_POLY_COMPRESS_D5
#endif

/* mlkem/native/x86_64/src/default_impl.h */
#if defined(MLKEM_USE_NATIVE_POLY_DECOMPRESS_D10)
#undef MLKEM_USE_NATIVE_POLY_DECOMPRESS_D10
#endif

/* mlkem/native/x86_64/src/default_impl.h */
#if defined(MLKEM_USE_NATIVE_POLY_DECOMPRESS_D11)
#undef MLKEM_USE_NATIVE_POLY_DECOMPRESS_D11
#endif

/* mlkem/native/x86_64/src/default_impl.h */
#if defined(MLKEM_USE_NATIVE_POLY_DECOMPRESS_D4)
#undef MLKEM_USE_NATIVE_POLY_DECOMPRESS_D4
#endif

/* mlkem/native/x86_64/src/default_impl.h */
#if defined(MLKEM_USE_NATIVE_POLY_DECOMPRESS_D5)
#undef MLKEM_USE_NATIVE_POLY_DECOMPRESS_D5
#endif

/* mlkem/native/x86_64/src/default_impl.h */
#if defined(MLKEM_USE_NATIVE_POLY_FROMBYTES)
#undef MLKEM_USE_NATIVE_POLY_FROMBYTES
#endif

/* mlkem/native/x86_64/src/default_impl.h */
#if defined(MLKEM_USE_NATIVE_POLY_MULCACHE_COMPUTE)
#undef MLKEM_USE_NATIVE_POLY_MULCACHE_COMPUTE
#endif

/* mlkem/native/x86_64/src/default_impl.h */
#if defined(MLKEM_USE_NATIVE_POLY_REDUCE)
#undef MLKEM_USE_NATIVE_POLY_REDUCE
#endif

/* mlkem/native/x86_64/src/default_impl.h */
#if defined(MLKEM_USE_NATIVE_POLY_TOBYTES)
#undef MLKEM_USE_NATIVE_POLY_TOBYTES
#endif

/* mlkem/native/x86_64/src/default_impl.h */
#if defined(MLKEM_USE_NATIVE_POLY_TOMONT)
#undef MLKEM_USE_NATIVE_POLY_TOMONT
#endif

/* mlkem/native/x86_64/src/default_impl.h */
#if defined(MLKEM_USE_NATIVE_REJ_UNIFORM)
#undef MLKEM_USE_NATIVE_REJ_UNIFORM
#endif

#endif
#endif /* MLKEM_NATIVE_MONOBUILD_KEEP_SHARED_HEADERS */
