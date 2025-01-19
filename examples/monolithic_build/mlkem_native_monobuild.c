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

#include "mlkem/cbd.c"
#include "mlkem/debug/debug.c"
#include "mlkem/fips202/fips202.c"
#include "mlkem/fips202/fips202x4.c"
#include "mlkem/fips202/keccakf1600.c"
#include "mlkem/indcpa.c"
#include "mlkem/kem.c"
#include "mlkem/ntt.c"
#include "mlkem/poly.c"
#include "mlkem/polyvec.c"
#include "mlkem/rej_uniform.c"
#include "mlkem/verify.c"
#include "mlkem/zetas.c"


/*
 * Undo all #define directives from *.c or *.h files
 */

/* mlkem/common.h */
#if defined(FIPS202_ASM_NAMESPACE)
#undef FIPS202_ASM_NAMESPACE
#endif

/* mlkem/common.h */
#if defined(FIPS202_NAMESPACE)
#undef FIPS202_NAMESPACE
#endif

/* mlkem/common.h */
#if defined(MLKEM_ASM_NAMESPACE)
#undef MLKEM_ASM_NAMESPACE
#endif

/* mlkem/common.h */
#if defined(MLKEM_ASM_NAMESPACE_K)
#undef MLKEM_ASM_NAMESPACE_K
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
#if defined(FIPS202_DEFAULT_NAMESPACE_PREFIX)
#undef FIPS202_DEFAULT_NAMESPACE_PREFIX
#endif

/* mlkem/config.h */
#if defined(FIPS202_NAMESPACE_PREFIX)
#undef FIPS202_NAMESPACE_PREFIX
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
#if defined(MLKEM_NATIVE_ARITH_BACKEND)
#undef MLKEM_NATIVE_ARITH_BACKEND
#endif

/* mlkem/config.h */
#if defined(MLKEM_NATIVE_CONFIG_H)
#undef MLKEM_NATIVE_CONFIG_H
#endif

/* mlkem/config.h */
#if defined(MLKEM_NATIVE_FIPS202_BACKEND)
#undef MLKEM_NATIVE_FIPS202_BACKEND
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
#if defined(INDCPA_H)
#undef INDCPA_H
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
#if defined(KEM_H)
#undef KEM_H
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
#if defined(PARAMS_H)
#undef PARAMS_H
#endif

/* mlkem/params.h */
#if defined(UINT12_LIMIT)
#undef UINT12_LIMIT
#endif

/* mlkem/polyvec.c */
#if defined(poly_cbd_eta1)
#undef poly_cbd_eta1
#endif

/* mlkem/polyvec.c */
#if defined(poly_cbd_eta2)
#undef poly_cbd_eta2
#endif

/* mlkem/polyvec.h */
#if defined(POLYVEC_H)
#undef POLYVEC_H
#endif

/* mlkem/polyvec.h */
#if defined(poly_compress_du)
#undef poly_compress_du
#endif

/* mlkem/polyvec.h */
#if defined(poly_compress_dv)
#undef poly_compress_dv
#endif

/* mlkem/polyvec.h */
#if defined(poly_decompress_du)
#undef poly_decompress_du
#endif

/* mlkem/polyvec.h */
#if defined(poly_decompress_dv)
#undef poly_decompress_dv
#endif

/* mlkem/polyvec.h */
#if defined(poly_getnoise_eta1122_4x)
#undef poly_getnoise_eta1122_4x
#endif

/* mlkem/polyvec.h */
#if defined(poly_getnoise_eta1_4x)
#undef poly_getnoise_eta1_4x
#endif

/* mlkem/polyvec.h */
#if defined(poly_getnoise_eta2)
#undef poly_getnoise_eta2
#endif

/* mlkem/polyvec.h */
#if defined(poly_getnoise_eta2_4x)
#undef poly_getnoise_eta2_4x
#endif

/* mlkem/polyvec.h */
#if defined(polyvec)
#undef polyvec
#endif

/* mlkem/polyvec.h */
#if defined(polyvec_add)
#undef polyvec_add
#endif

/* mlkem/polyvec.h */
#if defined(polyvec_basemul_acc_montgomery)
#undef polyvec_basemul_acc_montgomery
#endif

/* mlkem/polyvec.h */
#if defined(polyvec_basemul_acc_montgomery_cached)
#undef polyvec_basemul_acc_montgomery_cached
#endif

/* mlkem/polyvec.h */
#if defined(polyvec_compress_du)
#undef polyvec_compress_du
#endif

/* mlkem/polyvec.h */
#if defined(polyvec_decompress_du)
#undef polyvec_decompress_du
#endif

/* mlkem/polyvec.h */
#if defined(polyvec_frombytes)
#undef polyvec_frombytes
#endif

/* mlkem/polyvec.h */
#if defined(polyvec_invntt_tomont)
#undef polyvec_invntt_tomont
#endif

/* mlkem/polyvec.h */
#if defined(polyvec_mulcache)
#undef polyvec_mulcache
#endif

/* mlkem/polyvec.h */
#if defined(polyvec_mulcache_compute)
#undef polyvec_mulcache_compute
#endif

/* mlkem/polyvec.h */
#if defined(polyvec_ntt)
#undef polyvec_ntt
#endif

/* mlkem/polyvec.h */
#if defined(polyvec_reduce)
#undef polyvec_reduce
#endif

/* mlkem/polyvec.h */
#if defined(polyvec_tobytes)
#undef polyvec_tobytes
#endif

/* mlkem/polyvec.h */
#if defined(polyvec_tomont)
#undef polyvec_tomont
#endif


#if !defined(MLKEM_NATIVE_MONOBUILD_KEEP_SHARED_HEADERS)

/*
 * Undo all #define directives from *.c or *.h files
 */

/* mlkem/arith_backend.h */
#if defined(MLKEM_NATIVE_ARITH_IMPL_H)
#undef MLKEM_NATIVE_ARITH_IMPL_H
#endif

/* mlkem/cbd.c */
#if defined(empty_cu_cbd)
#undef empty_cu_cbd
#endif

/* mlkem/cbd.c */
#if defined(load24_littleendian)
#undef load24_littleendian
#endif

/* mlkem/cbd.c */
#if defined(load32_littleendian)
#undef load32_littleendian
#endif

/* mlkem/cbd.h */
#if defined(CBD_H)
#undef CBD_H
#endif

/* mlkem/cbd.h */
#if defined(poly_cbd2)
#undef poly_cbd2
#endif

/* mlkem/cbd.h */
#if defined(poly_cbd3)
#undef poly_cbd3
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

/* mlkem/debug/debug.c */
#if defined(MLKEM_NATIVE_DEBUG_ERROR_HEADER)
#undef MLKEM_NATIVE_DEBUG_ERROR_HEADER
#endif

/* mlkem/debug/debug.c */
#if defined(empty_cu_debug)
#undef empty_cu_debug
#endif

/* mlkem/debug/debug.h */
#if defined(MLKEM_DEBUG_H)
#undef MLKEM_DEBUG_H
#endif

/* mlkem/debug/debug.h */
#if defined(debug_assert)
#undef debug_assert
#endif

/* mlkem/debug/debug.h */
#if defined(debug_assert_abs_bound)
#undef debug_assert_abs_bound
#endif

/* mlkem/debug/debug.h */
#if defined(debug_assert_abs_bound_2d)
#undef debug_assert_abs_bound_2d
#endif

/* mlkem/debug/debug.h */
#if defined(debug_assert_bound)
#undef debug_assert_bound
#endif

/* mlkem/debug/debug.h */
#if defined(debug_assert_bound_2d)
#undef debug_assert_bound_2d
#endif

/* mlkem/debug/debug.h */
#if defined(mlkem_debug_assert)
#undef mlkem_debug_assert
#endif

/* mlkem/debug/debug.h */
#if defined(mlkem_debug_check_bounds)
#undef mlkem_debug_check_bounds
#endif

/* mlkem/fips202/fips202.c */
#if defined(empty_cu_fips202)
#undef empty_cu_fips202
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
#if defined(FIPS202_H)
#undef FIPS202_H
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
#if defined(MLKEM_NATIVE_FIPS202_IMPL_H)
#undef MLKEM_NATIVE_FIPS202_IMPL_H
#endif

/* mlkem/fips202/fips202x4.c */
#if defined(empty_cu_fips202x4)
#undef empty_cu_fips202x4
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
#if defined(FIPS_202X4_H)
#undef FIPS_202X4_H
#endif

/* mlkem/fips202/fips202x4.h */
#if defined(shake128x4_absorb_once)
#undef shake128x4_absorb_once
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

/* mlkem/fips202/keccakf1600.c */
#if defined(empty_cu_keccakf1600)
#undef empty_cu_keccakf1600
#endif

/* mlkem/fips202/keccakf1600.h */
#if defined(KECCAKF1600_H)
#undef KECCAKF1600_H
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

/* mlkem/ntt.c */
#if defined(empty_cu_ntt)
#undef empty_cu_ntt
#endif

/* mlkem/ntt.c */
#if defined(invntt_layer)
#undef invntt_layer
#endif

/* mlkem/ntt.c */
#if defined(ntt_butterfly_block)
#undef ntt_butterfly_block
#endif

/* mlkem/ntt.c */
#if defined(ntt_layer)
#undef ntt_layer
#endif

/* mlkem/ntt.h */
#if defined(NTT_H)
#undef NTT_H
#endif

/* mlkem/ntt.h */
#if defined(basemul_cached)
#undef basemul_cached
#endif

/* mlkem/ntt.h */
#if defined(poly_invntt_tomont)
#undef poly_invntt_tomont
#endif

/* mlkem/ntt.h */
#if defined(poly_ntt)
#undef poly_ntt
#endif

/* mlkem/ntt.h */
#if defined(zetas)
#undef zetas
#endif

/* mlkem/poly.c */
#if defined(empty_cu_poly)
#undef empty_cu_poly
#endif

/* mlkem/poly.h */
#if defined(INVNTT_BOUND)
#undef INVNTT_BOUND
#endif

/* mlkem/poly.h */
#if defined(NTT_BOUND)
#undef NTT_BOUND
#endif

/* mlkem/poly.h */
#if defined(POLY_H)
#undef POLY_H
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
#if defined(poly_basemul_montgomery_cached)
#undef poly_basemul_montgomery_cached
#endif

/* mlkem/poly.h */
#if defined(poly_compress_d10)
#undef poly_compress_d10
#endif

/* mlkem/poly.h */
#if defined(poly_compress_d11)
#undef poly_compress_d11
#endif

/* mlkem/poly.h */
#if defined(poly_compress_d4)
#undef poly_compress_d4
#endif

/* mlkem/poly.h */
#if defined(poly_compress_d5)
#undef poly_compress_d5
#endif

/* mlkem/poly.h */
#if defined(poly_decompress_d10)
#undef poly_decompress_d10
#endif

/* mlkem/poly.h */
#if defined(poly_decompress_d11)
#undef poly_decompress_d11
#endif

/* mlkem/poly.h */
#if defined(poly_decompress_d4)
#undef poly_decompress_d4
#endif

/* mlkem/poly.h */
#if defined(poly_decompress_d5)
#undef poly_decompress_d5
#endif

/* mlkem/poly.h */
#if defined(poly_frombytes)
#undef poly_frombytes
#endif

/* mlkem/poly.h */
#if defined(poly_frommsg)
#undef poly_frommsg
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
#if defined(poly_reduce)
#undef poly_reduce
#endif

/* mlkem/poly.h */
#if defined(poly_sub)
#undef poly_sub
#endif

/* mlkem/poly.h */
#if defined(poly_tobytes)
#undef poly_tobytes
#endif

/* mlkem/poly.h */
#if defined(poly_tomont)
#undef poly_tomont
#endif

/* mlkem/poly.h */
#if defined(poly_tomsg)
#undef poly_tomsg
#endif

/* mlkem/poly.h */
#if defined(scalar_compress_d1)
#undef scalar_compress_d1
#endif

/* mlkem/poly.h */
#if defined(scalar_compress_d10)
#undef scalar_compress_d10
#endif

/* mlkem/poly.h */
#if defined(scalar_compress_d11)
#undef scalar_compress_d11
#endif

/* mlkem/poly.h */
#if defined(scalar_compress_d4)
#undef scalar_compress_d4
#endif

/* mlkem/poly.h */
#if defined(scalar_compress_d5)
#undef scalar_compress_d5
#endif

/* mlkem/poly.h */
#if defined(scalar_decompress_d10)
#undef scalar_decompress_d10
#endif

/* mlkem/poly.h */
#if defined(scalar_decompress_d11)
#undef scalar_decompress_d11
#endif

/* mlkem/poly.h */
#if defined(scalar_decompress_d4)
#undef scalar_decompress_d4
#endif

/* mlkem/poly.h */
#if defined(scalar_decompress_d5)
#undef scalar_decompress_d5
#endif

/* mlkem/poly.h */
#if defined(scalar_signed_to_unsigned_q)
#undef scalar_signed_to_unsigned_q
#endif

/* mlkem/randombytes.h */
#if defined(RANDOMBYTES_H)
#undef RANDOMBYTES_H
#endif

/* mlkem/reduce.h */
#if defined(HALF_Q)
#undef HALF_Q
#endif

/* mlkem/reduce.h */
#if defined(REDUCE_H)
#undef REDUCE_H
#endif

/* mlkem/reduce.h */
#if defined(barrett_reduce)
#undef barrett_reduce
#endif

/* mlkem/reduce.h */
#if defined(cast_uint16_to_int16)
#undef cast_uint16_to_int16
#endif

/* mlkem/reduce.h */
#if defined(fqmul)
#undef fqmul
#endif

/* mlkem/reduce.h */
#if defined(montgomery_reduce)
#undef montgomery_reduce
#endif

/* mlkem/reduce.h */
#if defined(montgomery_reduce_generic)
#undef montgomery_reduce_generic
#endif

/* mlkem/rej_uniform.c */
#if defined(MLKEM_GEN_MATRIX_NBLOCKS)
#undef MLKEM_GEN_MATRIX_NBLOCKS
#endif

/* mlkem/rej_uniform.c */
#if defined(empty_cu_rej_uniform)
#undef empty_cu_rej_uniform
#endif

/* mlkem/rej_uniform.c */
#if defined(rej_uniform)
#undef rej_uniform
#endif

/* mlkem/rej_uniform.c */
#if defined(rej_uniform_scalar)
#undef rej_uniform_scalar
#endif

/* mlkem/rej_uniform.h */
#if defined(REJ_UNIFORM_H)
#undef REJ_UNIFORM_H
#endif

/* mlkem/rej_uniform.h */
#if defined(poly_rej_uniform)
#undef poly_rej_uniform
#endif

/* mlkem/rej_uniform.h */
#if defined(poly_rej_uniform_x4)
#undef poly_rej_uniform_x4
#endif

/* mlkem/symmetric.h */
#if defined(SYMMETRIC_H)
#undef SYMMETRIC_H
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

/* mlkem/verify.c */
#if defined(empty_cu_verify)
#undef empty_cu_verify
#endif

/* mlkem/verify.h */
#if defined(MLKEM_USE_ASM_VALUE_BARRIER)
#undef MLKEM_USE_ASM_VALUE_BARRIER
#endif

/* mlkem/verify.h */
#if defined(VERIFY_H)
#undef VERIFY_H
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

/* mlkem/zetas.c */
#if defined(empty_cu_zetas)
#undef empty_cu_zetas
#endif

#endif /* MLKEM_NATIVE_MONOBUILD_KEEP_SHARED_HEADERS */
