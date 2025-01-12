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
#include "mlkem/indcpa.c"
#include "mlkem/kem.c"
#include "mlkem/native/aarch64/src/aarch64_zetas.c"
#include "mlkem/native/aarch64/src/rej_uniform_table.c"
#include "mlkem/native/x86_64/src/basemul.c"
#include "mlkem/native/x86_64/src/consts.c"
#include "mlkem/native/x86_64/src/rej_uniform_avx2.c"
#include "mlkem/native/x86_64/src/rej_uniform_table.c"
#include "mlkem/ntt.c"
#include "mlkem/poly.c"
#include "mlkem/polyvec.c"
#include "mlkem/rej_uniform.c"
#include "mlkem/verify.c"
#include "mlkem/zetas.c"

#if !defined(MLKEM_NATIVE_MONOBUILD_NO_FIPS202_SOURCES)
#include "mlkem/fips202/fips202.c"
#include "mlkem/fips202/fips202x4.c"
#include "mlkem/fips202/keccakf1600.c"
#include "mlkem/fips202/native/aarch64/src/keccakf1600_round_constants.c"
#include "mlkem/fips202/native/x86_64/src/KeccakP-1600-times4-SIMD256.c"
#endif /* MLKEM_NATIVE_MONOBUILD_NO_FIPS202_SOURCES */


/*
 * Undo all #define directives from *.c or *.h files
 */

/* mlkem/arith_backend.h */
#if defined(MLKEM_NATIVE_ARITH_IMPL_H)
#undef MLKEM_NATIVE_ARITH_IMPL_H
#endif

/* mlkem/cbd.c */
#if defined(load32_littleendian)
#undef load32_littleendian
#endif

/* mlkem/cbd.c */
#if defined(load24_littleendian)
#undef load24_littleendian
#endif

/* mlkem/cbd.c */
#if defined(cbd2)
#undef cbd2
#endif

/* mlkem/cbd.c */
#if defined(cbd3)
#undef cbd3
#endif

/* mlkem/cbd.h */
#if defined(CBD_H)
#undef CBD_H
#endif

/* mlkem/cbd.h */
#if defined(poly_cbd_eta1)
#undef poly_cbd_eta1
#endif

/* mlkem/cbd.h */
#if defined(poly_cbd_eta2)
#undef poly_cbd_eta2
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
#if defined(cassert)
#undef cassert
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
#if defined(assigns)
#undef assigns
#endif

/* mlkem/cbmc.h */
#if defined(requires)
#undef requires
#endif

/* mlkem/cbmc.h */
#if defined(ensures)
#undef ensures
#endif

/* mlkem/cbmc.h */
#if defined(invariant)
#undef invariant
#endif

/* mlkem/cbmc.h */
#if defined(decreases)
#undef decreases
#endif

/* mlkem/cbmc.h */
#if defined(cassert)
#undef cassert
#endif

/* mlkem/cbmc.h */
#if defined(assume)
#undef assume
#endif

/* mlkem/cbmc.h */
#if defined(return_value)
#undef return_value
#endif

/* mlkem/cbmc.h */
#if defined(object_whole)
#undef object_whole
#endif

/* mlkem/cbmc.h */
#if defined(memory_slice)
#undef memory_slice
#endif

/* mlkem/cbmc.h */
#if defined(same_object)
#undef same_object
#endif

/* mlkem/cbmc.h */
#if defined(memory_no_alias)
#undef memory_no_alias
#endif

/* mlkem/cbmc.h */
#if defined(readable)
#undef readable
#endif

/* mlkem/cbmc.h */
#if defined(writeable)
#undef writeable
#endif

/* mlkem/cbmc.h */
#if defined(old)
#undef old
#endif

/* mlkem/cbmc.h */
#if defined(loop_entry)
#undef loop_entry
#endif

/* mlkem/cbmc.h */
#if defined(forall)
#undef forall
#endif

/* mlkem/cbmc.h */
#if defined(EXISTS)
#undef EXISTS
#endif

/* mlkem/cbmc.h */
#if defined(CBMC_CONCAT_)
#undef CBMC_CONCAT_
#endif

/* mlkem/cbmc.h */
#if defined(CBMC_CONCAT)
#undef CBMC_CONCAT
#endif

/* mlkem/cbmc.h */
#if defined(array_bound_core)
#undef array_bound_core
#endif

/* mlkem/cbmc.h */
#if defined(array_bound)
#undef array_bound
#endif

/* mlkem/cbmc.h */
#if defined(array_abs_bound)
#undef array_abs_bound
#endif

/* mlkem/common.h */
#if defined(MLKEM_NATIVE_COMMON_H)
#undef MLKEM_NATIVE_COMMON_H
#endif

/* mlkem/common.h */
#if defined(MLKEM_NATIVE_ARITH_BACKEND_NAME)
#undef MLKEM_NATIVE_ARITH_BACKEND_NAME
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
#if defined(MLKEM_NATIVE_INTERNAL_API)
#undef MLKEM_NATIVE_INTERNAL_API
#endif

/* mlkem/common.h */
#if defined(MLKEM_NATIVE_MAKE_NAMESPACE_)
#undef MLKEM_NATIVE_MAKE_NAMESPACE_
#endif

/* mlkem/common.h */
#if defined(MLKEM_NATIVE_MAKE_NAMESPACE)
#undef MLKEM_NATIVE_MAKE_NAMESPACE
#endif

/* mlkem/common.h */
#if defined(FIPS202_NAMESPACE)
#undef FIPS202_NAMESPACE
#endif

/* mlkem/common.h */
#if defined(MLKEM_NAMESPACE)
#undef MLKEM_NAMESPACE
#endif

/* mlkem/common.h */
#if defined(MLKEM_ASM_NAMESPACE)
#undef MLKEM_ASM_NAMESPACE
#endif

/* mlkem/common.h */
#if defined(FIPS202_ASM_NAMESPACE)
#undef FIPS202_ASM_NAMESPACE
#endif

/* mlkem/common.h */
#if defined(_PREFIX_UNDERSCORE)
#undef _PREFIX_UNDERSCORE
#endif

/* mlkem/common.h */
#if defined(PREFIX_UNDERSCORE)
#undef PREFIX_UNDERSCORE
#endif

/* mlkem/common.h */
#if defined(MLKEM_ASM_NAMESPACE)
#undef MLKEM_ASM_NAMESPACE
#endif

/* mlkem/common.h */
#if defined(FIPS202_ASM_NAMESPACE)
#undef FIPS202_ASM_NAMESPACE
#endif

/* mlkem/config.h */
#if defined(MLKEM_NATIVE_CONFIG_H)
#undef MLKEM_NATIVE_CONFIG_H
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
#if defined(FIPS202_NAMESPACE_PREFIX)
#undef FIPS202_NAMESPACE_PREFIX
#endif

/* mlkem/config.h */
#if defined(MLKEM_NATIVE_ARITH_BACKEND)
#undef MLKEM_NATIVE_ARITH_BACKEND
#endif

/* mlkem/config.h */
#if defined(MLKEM_NATIVE_FIPS202_BACKEND)
#undef MLKEM_NATIVE_FIPS202_BACKEND
#endif

/* mlkem/config.h */
#if defined(FIPS202_DEFAULT_NAMESPACE_PREFIX)
#undef FIPS202_DEFAULT_NAMESPACE_PREFIX
#endif

/* mlkem/config.h */
#if defined(MLKEM_DEFAULT_NAMESPACE_PREFIX)
#undef MLKEM_DEFAULT_NAMESPACE_PREFIX
#endif

/* mlkem/config.h */
#if defined(MLKEM_DEFAULT_NAMESPACE_PREFIX)
#undef MLKEM_DEFAULT_NAMESPACE_PREFIX
#endif

/* mlkem/config.h */
#if defined(MLKEM_DEFAULT_NAMESPACE_PREFIX)
#undef MLKEM_DEFAULT_NAMESPACE_PREFIX
#endif

/* mlkem/debug/debug.c */
#if defined(_ISOC99_SOURCE)
#undef _ISOC99_SOURCE
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
#if defined(mlkem_debug_assert)
#undef mlkem_debug_assert
#endif

/* mlkem/debug/debug.h */
#if defined(mlkem_debug_check_bounds)
#undef mlkem_debug_check_bounds
#endif

/* mlkem/debug/debug.h */
#if defined(mlkem_debug_print_error)
#undef mlkem_debug_print_error
#endif

/* mlkem/debug/debug.h */
#if defined(CASSERT)
#undef CASSERT
#endif

/* mlkem/debug/debug.h */
#if defined(SCALAR_BOUND)
#undef SCALAR_BOUND
#endif

/* mlkem/debug/debug.h */
#if defined(UBOUND)
#undef UBOUND
#endif

/* mlkem/debug/debug.h */
#if defined(BOUND)
#undef BOUND
#endif

/* mlkem/debug/debug.h */
#if defined(POLY_BOUND_MSG)
#undef POLY_BOUND_MSG
#endif

/* mlkem/debug/debug.h */
#if defined(POLY_UBOUND_MSG)
#undef POLY_UBOUND_MSG
#endif

/* mlkem/debug/debug.h */
#if defined(POLY_BOUND)
#undef POLY_BOUND
#endif

/* mlkem/debug/debug.h */
#if defined(POLY_UBOUND)
#undef POLY_UBOUND
#endif

/* mlkem/debug/debug.h */
#if defined(POLYVEC_BOUND)
#undef POLYVEC_BOUND
#endif

/* mlkem/debug/debug.h */
#if defined(POLYVEC_UBOUND)
#undef POLYVEC_UBOUND
#endif

/* mlkem/debug/debug.h */
#if defined(MLKEM_CONCAT_)
#undef MLKEM_CONCAT_
#endif

/* mlkem/debug/debug.h */
#if defined(MLKEM_CONCAT)
#undef MLKEM_CONCAT
#endif

/* mlkem/debug/debug.h */
#if defined(MLKEM_STATIC_ASSERT_DEFINE)
#undef MLKEM_STATIC_ASSERT_DEFINE
#endif

/* mlkem/debug/debug.h */
#if defined(MLKEM_STATIC_ASSERT_ADD_LINE0)
#undef MLKEM_STATIC_ASSERT_ADD_LINE0
#endif

/* mlkem/debug/debug.h */
#if defined(MLKEM_STATIC_ASSERT_ADD_LINE1)
#undef MLKEM_STATIC_ASSERT_ADD_LINE1
#endif

/* mlkem/debug/debug.h */
#if defined(MLKEM_STATIC_ASSERT_ADD_LINE2)
#undef MLKEM_STATIC_ASSERT_ADD_LINE2
#endif

/* mlkem/debug/debug.h */
#if defined(MLKEM_STATIC_ASSERT_ADD_ERROR)
#undef MLKEM_STATIC_ASSERT_ADD_ERROR
#endif

/* mlkem/debug/debug.h */
#if defined(STATIC_ASSERT)
#undef STATIC_ASSERT
#endif

/* mlkem/debug/debug.h */
#if defined(CASSERT)
#undef CASSERT
#endif

/* mlkem/debug/debug.h */
#if defined(SCALAR_BOUND)
#undef SCALAR_BOUND
#endif

/* mlkem/debug/debug.h */
#if defined(BOUND)
#undef BOUND
#endif

/* mlkem/debug/debug.h */
#if defined(POLY_BOUND)
#undef POLY_BOUND
#endif

/* mlkem/debug/debug.h */
#if defined(POLYVEC_BOUND)
#undef POLYVEC_BOUND
#endif

/* mlkem/debug/debug.h */
#if defined(POLY_BOUND_MSG)
#undef POLY_BOUND_MSG
#endif

/* mlkem/debug/debug.h */
#if defined(UBOUND)
#undef UBOUND
#endif

/* mlkem/debug/debug.h */
#if defined(POLY_UBOUND)
#undef POLY_UBOUND
#endif

/* mlkem/debug/debug.h */
#if defined(POLYVEC_UBOUND)
#undef POLYVEC_UBOUND
#endif

/* mlkem/debug/debug.h */
#if defined(POLY_UBOUND_MSG)
#undef POLY_UBOUND_MSG
#endif

/* mlkem/debug/debug.h */
#if defined(STATIC_ASSERT)
#undef STATIC_ASSERT
#endif

/* mlkem/indcpa.c */
#if defined(pack_pk)
#undef pack_pk
#endif

/* mlkem/indcpa.c */
#if defined(unpack_pk)
#undef unpack_pk
#endif

/* mlkem/indcpa.c */
#if defined(pack_sk)
#undef pack_sk
#endif

/* mlkem/indcpa.c */
#if defined(unpack_sk)
#undef unpack_sk
#endif

/* mlkem/indcpa.c */
#if defined(pack_ciphertext)
#undef pack_ciphertext
#endif

/* mlkem/indcpa.c */
#if defined(unpack_ciphertext)
#undef unpack_ciphertext
#endif

/* mlkem/indcpa.c */
#if defined(gen_matrix_entry_x4)
#undef gen_matrix_entry_x4
#endif

/* mlkem/indcpa.c */
#if defined(gen_matrix_entry)
#undef gen_matrix_entry
#endif

/* mlkem/indcpa.c */
#if defined(matvec_mul)
#undef matvec_mul
#endif

/* mlkem/indcpa.c */
#if defined(MLKEM_GEN_MATRIX_NBLOCKS)
#undef MLKEM_GEN_MATRIX_NBLOCKS
#endif

/* mlkem/indcpa.c */
#if defined(poly_permute_bitrev_to_custom)
#undef poly_permute_bitrev_to_custom
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
#if defined(indcpa_keypair_derand)
#undef indcpa_keypair_derand
#endif

/* mlkem/indcpa.h */
#if defined(indcpa_enc)
#undef indcpa_enc
#endif

/* mlkem/indcpa.h */
#if defined(indcpa_dec)
#undef indcpa_dec
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

/* mlkem/mlkem_native.h */
#if defined(MLKEM_NATIVE_H)
#undef MLKEM_NATIVE_H
#endif

/* mlkem/mlkem_native.h */
#if defined(BUILD_INFO_LVL)
#undef BUILD_INFO_LVL
#endif

/* mlkem/mlkem_native.h */
#if defined(BUILD_INFO_LVL)
#undef BUILD_INFO_LVL
#endif

/* mlkem/mlkem_native.h */
#if defined(BUILD_INFO_LVL)
#undef BUILD_INFO_LVL
#endif

/* mlkem/mlkem_native.h */
#if defined(BUILD_INFO_CONCAT_)
#undef BUILD_INFO_CONCAT_
#endif

/* mlkem/mlkem_native.h */
#if defined(BUILD_INFO_CONCAT)
#undef BUILD_INFO_CONCAT
#endif

/* mlkem/mlkem_native.h */
#if defined(BUILD_INFO_NAMESPACE)
#undef BUILD_INFO_NAMESPACE
#endif

/* mlkem/mlkem_native.h */
#if defined(MLKEM512_SECRETKEYBYTES)
#undef MLKEM512_SECRETKEYBYTES
#endif

/* mlkem/mlkem_native.h */
#if defined(MLKEM512_PUBLICKEYBYTES)
#undef MLKEM512_PUBLICKEYBYTES
#endif

/* mlkem/mlkem_native.h */
#if defined(MLKEM512_CIPHERTEXTBYTES)
#undef MLKEM512_CIPHERTEXTBYTES
#endif

/* mlkem/mlkem_native.h */
#if defined(MLKEM768_SECRETKEYBYTES)
#undef MLKEM768_SECRETKEYBYTES
#endif

/* mlkem/mlkem_native.h */
#if defined(MLKEM768_PUBLICKEYBYTES)
#undef MLKEM768_PUBLICKEYBYTES
#endif

/* mlkem/mlkem_native.h */
#if defined(MLKEM768_CIPHERTEXTBYTES)
#undef MLKEM768_CIPHERTEXTBYTES
#endif

/* mlkem/mlkem_native.h */
#if defined(MLKEM1024_SECRETKEYBYTES)
#undef MLKEM1024_SECRETKEYBYTES
#endif

/* mlkem/mlkem_native.h */
#if defined(MLKEM1024_PUBLICKEYBYTES)
#undef MLKEM1024_PUBLICKEYBYTES
#endif

/* mlkem/mlkem_native.h */
#if defined(MLKEM1024_CIPHERTEXTBYTES)
#undef MLKEM1024_CIPHERTEXTBYTES
#endif

/* mlkem/mlkem_native.h */
#if defined(MLKEM_SYMBYTES)
#undef MLKEM_SYMBYTES
#endif

/* mlkem/mlkem_native.h */
#if defined(MLKEM512_SYMBYTES)
#undef MLKEM512_SYMBYTES
#endif

/* mlkem/mlkem_native.h */
#if defined(MLKEM768_SYMBYTES)
#undef MLKEM768_SYMBYTES
#endif

/* mlkem/mlkem_native.h */
#if defined(MLKEM1024_SYMBYTES)
#undef MLKEM1024_SYMBYTES
#endif

/* mlkem/mlkem_native.h */
#if defined(MLKEM_BYTES)
#undef MLKEM_BYTES
#endif

/* mlkem/mlkem_native.h */
#if defined(MLKEM512_BYTES)
#undef MLKEM512_BYTES
#endif

/* mlkem/mlkem_native.h */
#if defined(MLKEM768_BYTES)
#undef MLKEM768_BYTES
#endif

/* mlkem/mlkem_native.h */
#if defined(MLKEM1024_BYTES)
#undef MLKEM1024_BYTES
#endif

/* mlkem/mlkem_native.h */
#if defined(MLKEM_SECRETKEYBYTES_)
#undef MLKEM_SECRETKEYBYTES_
#endif

/* mlkem/mlkem_native.h */
#if defined(MLKEM_PUBLICKEYBYTES_)
#undef MLKEM_PUBLICKEYBYTES_
#endif

/* mlkem/mlkem_native.h */
#if defined(MLKEM_CIPHERTEXTBYTES_)
#undef MLKEM_CIPHERTEXTBYTES_
#endif

/* mlkem/mlkem_native.h */
#if defined(MLKEM_SECRETKEYBYTES)
#undef MLKEM_SECRETKEYBYTES
#endif

/* mlkem/mlkem_native.h */
#if defined(MLKEM_PUBLICKEYBYTES)
#undef MLKEM_PUBLICKEYBYTES
#endif

/* mlkem/mlkem_native.h */
#if defined(MLKEM_CIPHERTEXTBYTES)
#undef MLKEM_CIPHERTEXTBYTES
#endif

/* mlkem/mlkem_native.h */
#if defined(CRYPTO_SECRETKEYBYTES)
#undef CRYPTO_SECRETKEYBYTES
#endif

/* mlkem/mlkem_native.h */
#if defined(CRYPTO_PUBLICKEYBYTES)
#undef CRYPTO_PUBLICKEYBYTES
#endif

/* mlkem/mlkem_native.h */
#if defined(CRYPTO_CIPHERTEXTBYTES)
#undef CRYPTO_CIPHERTEXTBYTES
#endif

/* mlkem/mlkem_native.h */
#if defined(CRYPTO_SYMBYTES)
#undef CRYPTO_SYMBYTES
#endif

/* mlkem/mlkem_native.h */
#if defined(CRYPTO_BYTES)
#undef CRYPTO_BYTES
#endif

/* mlkem/mlkem_native.h */
#if defined(crypto_kem_keypair_derand)
#undef crypto_kem_keypair_derand
#endif

/* mlkem/mlkem_native.h */
#if defined(crypto_kem_keypair)
#undef crypto_kem_keypair
#endif

/* mlkem/mlkem_native.h */
#if defined(crypto_kem_enc_derand)
#undef crypto_kem_enc_derand
#endif

/* mlkem/mlkem_native.h */
#if defined(crypto_kem_enc)
#undef crypto_kem_enc
#endif

/* mlkem/mlkem_native.h */
#if defined(crypto_kem_dec)
#undef crypto_kem_dec
#endif

/* mlkem/native/aarch64/clean.h */
#if defined(MLKEM_NATIVE_ARITH_PROFILE_H)
#undef MLKEM_NATIVE_ARITH_PROFILE_H
#endif

/* mlkem/native/aarch64/clean.h */
#if defined(MLKEM_NATIVE_ARITH_BACKEND_AARCH64_CLEAN)
#undef MLKEM_NATIVE_ARITH_BACKEND_AARCH64_CLEAN
#endif

/* mlkem/native/aarch64/clean.h */
#if defined(MLKEM_NATIVE_ARITH_BACKEND_NAME)
#undef MLKEM_NATIVE_ARITH_BACKEND_NAME
#endif

/* mlkem/native/aarch64/clean.h */
#if defined(MLKEM_NATIVE_ARITH_BACKEND_IMPL)
#undef MLKEM_NATIVE_ARITH_BACKEND_IMPL
#endif

/* mlkem/native/aarch64/opt.h */
#if defined(MLKEM_NATIVE_ARITH_PROFILE_H)
#undef MLKEM_NATIVE_ARITH_PROFILE_H
#endif

/* mlkem/native/aarch64/opt.h */
#if defined(MLKEM_NATIVE_ARITH_BACKEND_AARCH64_OPT)
#undef MLKEM_NATIVE_ARITH_BACKEND_AARCH64_OPT
#endif

/* mlkem/native/aarch64/opt.h */
#if defined(MLKEM_NATIVE_ARITH_BACKEND_NAME)
#undef MLKEM_NATIVE_ARITH_BACKEND_NAME
#endif

/* mlkem/native/aarch64/opt.h */
#if defined(MLKEM_NATIVE_ARITH_BACKEND_IMPL)
#undef MLKEM_NATIVE_ARITH_BACKEND_IMPL
#endif

/* mlkem/native/aarch64/src/aarch64_zetas.c */
#if defined(empty_cu_aarch64_zetas)
#undef empty_cu_aarch64_zetas
#endif

/* mlkem/native/aarch64/src/arith_native_aarch64.h */
#if defined(MLKEM_AARCH64_NATIVE_H)
#undef MLKEM_AARCH64_NATIVE_H
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
#if defined(aarch64_invntt_zetas_layer01234)
#undef aarch64_invntt_zetas_layer01234
#endif

/* mlkem/native/aarch64/src/arith_native_aarch64.h */
#if defined(aarch64_invntt_zetas_layer56)
#undef aarch64_invntt_zetas_layer56
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
#if defined(rej_uniform_table)
#undef rej_uniform_table
#endif

/* mlkem/native/aarch64/src/arith_native_aarch64.h */
#if defined(ntt_asm_clean)
#undef ntt_asm_clean
#endif

/* mlkem/native/aarch64/src/arith_native_aarch64.h */
#if defined(ntt_asm_opt)
#undef ntt_asm_opt
#endif

/* mlkem/native/aarch64/src/arith_native_aarch64.h */
#if defined(intt_asm_clean)
#undef intt_asm_clean
#endif

/* mlkem/native/aarch64/src/arith_native_aarch64.h */
#if defined(intt_asm_opt)
#undef intt_asm_opt
#endif

/* mlkem/native/aarch64/src/arith_native_aarch64.h */
#if defined(rej_uniform_asm_clean)
#undef rej_uniform_asm_clean
#endif

/* mlkem/native/aarch64/src/arith_native_aarch64.h */
#if defined(poly_reduce_asm_clean)
#undef poly_reduce_asm_clean
#endif

/* mlkem/native/aarch64/src/arith_native_aarch64.h */
#if defined(poly_reduce_asm_opt)
#undef poly_reduce_asm_opt
#endif

/* mlkem/native/aarch64/src/arith_native_aarch64.h */
#if defined(poly_tomont_asm_clean)
#undef poly_tomont_asm_clean
#endif

/* mlkem/native/aarch64/src/arith_native_aarch64.h */
#if defined(poly_tomont_asm_opt)
#undef poly_tomont_asm_opt
#endif

/* mlkem/native/aarch64/src/arith_native_aarch64.h */
#if defined(poly_mulcache_compute_asm_clean)
#undef poly_mulcache_compute_asm_clean
#endif

/* mlkem/native/aarch64/src/arith_native_aarch64.h */
#if defined(poly_mulcache_compute_asm_opt)
#undef poly_mulcache_compute_asm_opt
#endif

/* mlkem/native/aarch64/src/arith_native_aarch64.h */
#if defined(poly_tobytes_asm_clean)
#undef poly_tobytes_asm_clean
#endif

/* mlkem/native/aarch64/src/arith_native_aarch64.h */
#if defined(poly_tobytes_asm_opt)
#undef poly_tobytes_asm_opt
#endif

/* mlkem/native/aarch64/src/arith_native_aarch64.h */
#if defined(polyvec_basemul_acc_montgomery_cached_asm_clean)
#undef polyvec_basemul_acc_montgomery_cached_asm_clean
#endif

/* mlkem/native/aarch64/src/arith_native_aarch64.h */
#if defined(polyvec_basemul_acc_montgomery_cached_asm_opt)
#undef polyvec_basemul_acc_montgomery_cached_asm_opt
#endif

/* mlkem/native/aarch64/src/clean_impl.h */
#if defined(MLKEM_NATIVE_ARITH_PROFILE_IMPL_H)
#undef MLKEM_NATIVE_ARITH_PROFILE_IMPL_H
#endif

/* mlkem/native/aarch64/src/clean_impl.h */
#if defined(MLKEM_USE_NATIVE_NTT)
#undef MLKEM_USE_NATIVE_NTT
#endif

/* mlkem/native/aarch64/src/clean_impl.h */
#if defined(MLKEM_USE_NATIVE_INTT)
#undef MLKEM_USE_NATIVE_INTT
#endif

/* mlkem/native/aarch64/src/clean_impl.h */
#if defined(MLKEM_USE_NATIVE_POLY_REDUCE)
#undef MLKEM_USE_NATIVE_POLY_REDUCE
#endif

/* mlkem/native/aarch64/src/clean_impl.h */
#if defined(MLKEM_USE_NATIVE_POLY_TOMONT)
#undef MLKEM_USE_NATIVE_POLY_TOMONT
#endif

/* mlkem/native/aarch64/src/clean_impl.h */
#if defined(MLKEM_USE_NATIVE_POLY_MULCACHE_COMPUTE)
#undef MLKEM_USE_NATIVE_POLY_MULCACHE_COMPUTE
#endif

/* mlkem/native/aarch64/src/clean_impl.h */
#if defined(MLKEM_USE_NATIVE_POLYVEC_BASEMUL_ACC_MONTGOMERY_CACHED)
#undef MLKEM_USE_NATIVE_POLYVEC_BASEMUL_ACC_MONTGOMERY_CACHED
#endif

/* mlkem/native/aarch64/src/clean_impl.h */
#if defined(MLKEM_USE_NATIVE_POLY_TOBYTES)
#undef MLKEM_USE_NATIVE_POLY_TOBYTES
#endif

/* mlkem/native/aarch64/src/clean_impl.h */
#if defined(MLKEM_USE_NATIVE_REJ_UNIFORM)
#undef MLKEM_USE_NATIVE_REJ_UNIFORM
#endif

/* mlkem/native/aarch64/src/consts.h */
#if defined(MLKEM_NATIVE_AARCH64_CONSTS)
#undef MLKEM_NATIVE_AARCH64_CONSTS
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
#if defined(MLKEM_USE_NATIVE_NTT)
#undef MLKEM_USE_NATIVE_NTT
#endif

/* mlkem/native/aarch64/src/opt_impl.h */
#if defined(MLKEM_USE_NATIVE_INTT)
#undef MLKEM_USE_NATIVE_INTT
#endif

/* mlkem/native/aarch64/src/opt_impl.h */
#if defined(MLKEM_USE_NATIVE_POLY_REDUCE)
#undef MLKEM_USE_NATIVE_POLY_REDUCE
#endif

/* mlkem/native/aarch64/src/opt_impl.h */
#if defined(MLKEM_USE_NATIVE_POLY_TOMONT)
#undef MLKEM_USE_NATIVE_POLY_TOMONT
#endif

/* mlkem/native/aarch64/src/opt_impl.h */
#if defined(MLKEM_USE_NATIVE_POLY_MULCACHE_COMPUTE)
#undef MLKEM_USE_NATIVE_POLY_MULCACHE_COMPUTE
#endif

/* mlkem/native/aarch64/src/opt_impl.h */
#if defined(MLKEM_USE_NATIVE_POLYVEC_BASEMUL_ACC_MONTGOMERY_CACHED)
#undef MLKEM_USE_NATIVE_POLYVEC_BASEMUL_ACC_MONTGOMERY_CACHED
#endif

/* mlkem/native/aarch64/src/opt_impl.h */
#if defined(MLKEM_USE_NATIVE_POLY_TOBYTES)
#undef MLKEM_USE_NATIVE_POLY_TOBYTES
#endif

/* mlkem/native/aarch64/src/opt_impl.h */
#if defined(MLKEM_USE_NATIVE_REJ_UNIFORM)
#undef MLKEM_USE_NATIVE_REJ_UNIFORM
#endif

/* mlkem/native/aarch64/src/rej_uniform_table.c */
#if defined(empty_cu_aarch64_rej_uniform_table)
#undef empty_cu_aarch64_rej_uniform_table
#endif

/* mlkem/native/api.h */
#if defined(MLKEM_NATIVE_ARITH_NATIVE_API_H)
#undef MLKEM_NATIVE_ARITH_NATIVE_API_H
#endif

/* mlkem/native/default.h */
#if defined(MLKEM_NATIVE_ARITH_BACKEND_DEFAULT_H)
#undef MLKEM_NATIVE_ARITH_BACKEND_DEFAULT_H
#endif

/* mlkem/native/x86_64/default.h */
#if defined(MLKEM_NATIVE_ARITH_PROFILE_H)
#undef MLKEM_NATIVE_ARITH_PROFILE_H
#endif

/* mlkem/native/x86_64/default.h */
#if defined(MLKEM_NATIVE_ARITH_BACKEND_X86_64_DEFAULT)
#undef MLKEM_NATIVE_ARITH_BACKEND_X86_64_DEFAULT
#endif

/* mlkem/native/x86_64/default.h */
#if defined(MLKEM_NATIVE_ARITH_BACKEND_NAME)
#undef MLKEM_NATIVE_ARITH_BACKEND_NAME
#endif

/* mlkem/native/x86_64/default.h */
#if defined(MLKEM_NATIVE_ARITH_BACKEND_IMPL)
#undef MLKEM_NATIVE_ARITH_BACKEND_IMPL
#endif

/* mlkem/native/x86_64/src/align.h */
#if defined(ALIGN_H)
#undef ALIGN_H
#endif

/* mlkem/native/x86_64/src/align.h */
#if defined(ALIGNED_UINT8)
#undef ALIGNED_UINT8
#endif

/* mlkem/native/x86_64/src/align.h */
#if defined(ALIGNED_INT16)
#undef ALIGNED_INT16
#endif

/* mlkem/native/x86_64/src/arith_native_x86_64.h */
#if defined(MLKEM_X86_64_NATIVE_H)
#undef MLKEM_X86_64_NATIVE_H
#endif

/* mlkem/native/x86_64/src/arith_native_x86_64.h */
#if defined(REJ_UNIFORM_AVX_NBLOCKS)
#undef REJ_UNIFORM_AVX_NBLOCKS
#endif

/* mlkem/native/x86_64/src/arith_native_x86_64.h */
#if defined(REJ_UNIFORM_AVX_BUFLEN)
#undef REJ_UNIFORM_AVX_BUFLEN
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
#if defined(ntt_avx2)
#undef ntt_avx2
#endif

/* mlkem/native/x86_64/src/arith_native_x86_64.h */
#if defined(invntt_avx2)
#undef invntt_avx2
#endif

/* mlkem/native/x86_64/src/arith_native_x86_64.h */
#if defined(nttpack_avx2)
#undef nttpack_avx2
#endif

/* mlkem/native/x86_64/src/arith_native_x86_64.h */
#if defined(nttunpack_avx2)
#undef nttunpack_avx2
#endif

/* mlkem/native/x86_64/src/arith_native_x86_64.h */
#if defined(reduce_avx2)
#undef reduce_avx2
#endif

/* mlkem/native/x86_64/src/arith_native_x86_64.h */
#if defined(basemul_avx2)
#undef basemul_avx2
#endif

/* mlkem/native/x86_64/src/arith_native_x86_64.h */
#if defined(polyvec_basemul_acc_montgomery_cached_avx2)
#undef polyvec_basemul_acc_montgomery_cached_avx2
#endif

/* mlkem/native/x86_64/src/arith_native_x86_64.h */
#if defined(ntttobytes_avx2)
#undef ntttobytes_avx2
#endif

/* mlkem/native/x86_64/src/arith_native_x86_64.h */
#if defined(nttfrombytes_avx2)
#undef nttfrombytes_avx2
#endif

/* mlkem/native/x86_64/src/arith_native_x86_64.h */
#if defined(tomont_avx2)
#undef tomont_avx2
#endif

/* mlkem/native/x86_64/src/basemul.c */
#if defined(empty_cu_avx2_basemul)
#undef empty_cu_avx2_basemul
#endif

/* mlkem/native/x86_64/src/consts.c */
#if defined(Q)
#undef Q
#endif

/* mlkem/native/x86_64/src/consts.c */
#if defined(MONT)
#undef MONT
#endif

/* mlkem/native/x86_64/src/consts.c */
#if defined(QINV)
#undef QINV
#endif

/* mlkem/native/x86_64/src/consts.c */
#if defined(V)
#undef V
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
#if defined(MONTSQHI)
#undef MONTSQHI
#endif

/* mlkem/native/x86_64/src/consts.c */
#if defined(MONTSQLO)
#undef MONTSQLO
#endif

/* mlkem/native/x86_64/src/consts.c */
#if defined(MASK)
#undef MASK
#endif

/* mlkem/native/x86_64/src/consts.c */
#if defined(SHIFT)
#undef SHIFT
#endif

/* mlkem/native/x86_64/src/consts.c */
#if defined(_16XQ)
#undef _16XQ
#endif

/* mlkem/native/x86_64/src/consts.c */
#if defined(_16XQINV)
#undef _16XQINV
#endif

/* mlkem/native/x86_64/src/consts.c */
#if defined(_16XV)
#undef _16XV
#endif

/* mlkem/native/x86_64/src/consts.c */
#if defined(_16XFLO)
#undef _16XFLO
#endif

/* mlkem/native/x86_64/src/consts.c */
#if defined(_16XFHI)
#undef _16XFHI
#endif

/* mlkem/native/x86_64/src/consts.c */
#if defined(_16XMONTSQLO)
#undef _16XMONTSQLO
#endif

/* mlkem/native/x86_64/src/consts.c */
#if defined(_16XMONTSQHI)
#undef _16XMONTSQHI
#endif

/* mlkem/native/x86_64/src/consts.c */
#if defined(_16XMASK)
#undef _16XMASK
#endif

/* mlkem/native/x86_64/src/consts.c */
#if defined(_REVIDXB)
#undef _REVIDXB
#endif

/* mlkem/native/x86_64/src/consts.c */
#if defined(_REVIDXD)
#undef _REVIDXD
#endif

/* mlkem/native/x86_64/src/consts.c */
#if defined(_ZETAS_EXP)
#undef _ZETAS_EXP
#endif

/* mlkem/native/x86_64/src/consts.c */
#if defined(_16XSHIFT)
#undef _16XSHIFT
#endif

/* mlkem/native/x86_64/src/consts.c */
#if defined(empty_cu_consts)
#undef empty_cu_consts
#endif

/* mlkem/native/x86_64/src/consts.h */
#if defined(CONSTS_H)
#undef CONSTS_H
#endif

/* mlkem/native/x86_64/src/consts.h */
#if defined(_16XQ)
#undef _16XQ
#endif

/* mlkem/native/x86_64/src/consts.h */
#if defined(_16XQINV)
#undef _16XQINV
#endif

/* mlkem/native/x86_64/src/consts.h */
#if defined(_16XV)
#undef _16XV
#endif

/* mlkem/native/x86_64/src/consts.h */
#if defined(_16XFLO)
#undef _16XFLO
#endif

/* mlkem/native/x86_64/src/consts.h */
#if defined(_16XFHI)
#undef _16XFHI
#endif

/* mlkem/native/x86_64/src/consts.h */
#if defined(_16XMONTSQLO)
#undef _16XMONTSQLO
#endif

/* mlkem/native/x86_64/src/consts.h */
#if defined(_16XMONTSQHI)
#undef _16XMONTSQHI
#endif

/* mlkem/native/x86_64/src/consts.h */
#if defined(_16XMASK)
#undef _16XMASK
#endif

/* mlkem/native/x86_64/src/consts.h */
#if defined(_REVIDXB)
#undef _REVIDXB
#endif

/* mlkem/native/x86_64/src/consts.h */
#if defined(_REVIDXD)
#undef _REVIDXD
#endif

/* mlkem/native/x86_64/src/consts.h */
#if defined(_ZETAS_EXP)
#undef _ZETAS_EXP
#endif

/* mlkem/native/x86_64/src/consts.h */
#if defined(_16XSHIFT)
#undef _16XSHIFT
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
#if defined(MLKEM_USE_NATIVE_NTT_CUSTOM_ORDER)
#undef MLKEM_USE_NATIVE_NTT_CUSTOM_ORDER
#endif

/* mlkem/native/x86_64/src/default_impl.h */
#if defined(MLKEM_USE_NATIVE_REJ_UNIFORM)
#undef MLKEM_USE_NATIVE_REJ_UNIFORM
#endif

/* mlkem/native/x86_64/src/default_impl.h */
#if defined(MLKEM_USE_NATIVE_NTT)
#undef MLKEM_USE_NATIVE_NTT
#endif

/* mlkem/native/x86_64/src/default_impl.h */
#if defined(MLKEM_USE_NATIVE_INTT)
#undef MLKEM_USE_NATIVE_INTT
#endif

/* mlkem/native/x86_64/src/default_impl.h */
#if defined(MLKEM_USE_NATIVE_POLY_REDUCE)
#undef MLKEM_USE_NATIVE_POLY_REDUCE
#endif

/* mlkem/native/x86_64/src/default_impl.h */
#if defined(MLKEM_USE_NATIVE_POLY_TOMONT)
#undef MLKEM_USE_NATIVE_POLY_TOMONT
#endif

/* mlkem/native/x86_64/src/default_impl.h */
#if defined(MLKEM_USE_NATIVE_POLYVEC_BASEMUL_ACC_MONTGOMERY_CACHED)
#undef MLKEM_USE_NATIVE_POLYVEC_BASEMUL_ACC_MONTGOMERY_CACHED
#endif

/* mlkem/native/x86_64/src/default_impl.h */
#if defined(MLKEM_USE_NATIVE_POLY_MULCACHE_COMPUTE)
#undef MLKEM_USE_NATIVE_POLY_MULCACHE_COMPUTE
#endif

/* mlkem/native/x86_64/src/default_impl.h */
#if defined(MLKEM_USE_NATIVE_POLY_TOBYTES)
#undef MLKEM_USE_NATIVE_POLY_TOBYTES
#endif

/* mlkem/native/x86_64/src/default_impl.h */
#if defined(MLKEM_USE_NATIVE_POLY_FROMBYTES)
#undef MLKEM_USE_NATIVE_POLY_FROMBYTES
#endif

/* mlkem/native/x86_64/src/rej_uniform_avx2.c */
#if defined(_mm256_cmpge_epu16)
#undef _mm256_cmpge_epu16
#endif

/* mlkem/native/x86_64/src/rej_uniform_avx2.c */
#if defined(_mm_cmpge_epu16)
#undef _mm_cmpge_epu16
#endif

/* mlkem/native/x86_64/src/rej_uniform_avx2.c */
#if defined(empty_cu_rej_uniform_avx2)
#undef empty_cu_rej_uniform_avx2
#endif

/* mlkem/native/x86_64/src/rej_uniform_table.c */
#if defined(empty_cu_avx2_rej_uniform_table)
#undef empty_cu_avx2_rej_uniform_table
#endif

/* mlkem/ntt.c */
#if defined(ntt_butterfly_block)
#undef ntt_butterfly_block
#endif

/* mlkem/ntt.c */
#if defined(ntt_layer)
#undef ntt_layer
#endif

/* mlkem/ntt.c */
#if defined(invntt_layer)
#undef invntt_layer
#endif

/* mlkem/ntt.h */
#if defined(NTT_H)
#undef NTT_H
#endif

/* mlkem/ntt.h */
#if defined(zetas)
#undef zetas
#endif

/* mlkem/ntt.h */
#if defined(poly_ntt)
#undef poly_ntt
#endif

/* mlkem/ntt.h */
#if defined(poly_invntt_tomont)
#undef poly_invntt_tomont
#endif

/* mlkem/ntt.h */
#if defined(basemul_cached)
#undef basemul_cached
#endif

/* mlkem/params.h */
#if defined(PARAMS_H)
#undef PARAMS_H
#endif

/* mlkem/params.h */
#if defined(MLKEM_N)
#undef MLKEM_N
#endif

/* mlkem/params.h */
#if defined(MLKEM_Q)
#undef MLKEM_Q
#endif

/* mlkem/params.h */
#if defined(UINT12_LIMIT)
#undef UINT12_LIMIT
#endif

/* mlkem/params.h */
#if defined(MLKEM_SYMBYTES)
#undef MLKEM_SYMBYTES
#endif

/* mlkem/params.h */
#if defined(MLKEM_SSBYTES)
#undef MLKEM_SSBYTES
#endif

/* mlkem/params.h */
#if defined(MLKEM_POLYBYTES)
#undef MLKEM_POLYBYTES
#endif

/* mlkem/params.h */
#if defined(MLKEM_POLYVECBYTES)
#undef MLKEM_POLYVECBYTES
#endif

/* mlkem/params.h */
#if defined(MLKEM_LVL)
#undef MLKEM_LVL
#endif

/* mlkem/params.h */
#if defined(MLKEM_ETA1)
#undef MLKEM_ETA1
#endif

/* mlkem/params.h */
#if defined(MLKEM_POLYCOMPRESSEDBYTES_DV)
#undef MLKEM_POLYCOMPRESSEDBYTES_DV
#endif

/* mlkem/params.h */
#if defined(MLKEM_POLYCOMPRESSEDBYTES_DU)
#undef MLKEM_POLYCOMPRESSEDBYTES_DU
#endif

/* mlkem/params.h */
#if defined(MLKEM_POLYVECCOMPRESSEDBYTES_DU)
#undef MLKEM_POLYVECCOMPRESSEDBYTES_DU
#endif

/* mlkem/params.h */
#if defined(MLKEM_LVL)
#undef MLKEM_LVL
#endif

/* mlkem/params.h */
#if defined(MLKEM_ETA1)
#undef MLKEM_ETA1
#endif

/* mlkem/params.h */
#if defined(MLKEM_POLYCOMPRESSEDBYTES_DV)
#undef MLKEM_POLYCOMPRESSEDBYTES_DV
#endif

/* mlkem/params.h */
#if defined(MLKEM_POLYCOMPRESSEDBYTES_DU)
#undef MLKEM_POLYCOMPRESSEDBYTES_DU
#endif

/* mlkem/params.h */
#if defined(MLKEM_POLYVECCOMPRESSEDBYTES_DU)
#undef MLKEM_POLYVECCOMPRESSEDBYTES_DU
#endif

/* mlkem/params.h */
#if defined(MLKEM_LVL)
#undef MLKEM_LVL
#endif

/* mlkem/params.h */
#if defined(MLKEM_ETA1)
#undef MLKEM_ETA1
#endif

/* mlkem/params.h */
#if defined(MLKEM_POLYCOMPRESSEDBYTES_DV)
#undef MLKEM_POLYCOMPRESSEDBYTES_DV
#endif

/* mlkem/params.h */
#if defined(MLKEM_POLYCOMPRESSEDBYTES_DU)
#undef MLKEM_POLYCOMPRESSEDBYTES_DU
#endif

/* mlkem/params.h */
#if defined(MLKEM_POLYVECCOMPRESSEDBYTES_DU)
#undef MLKEM_POLYVECCOMPRESSEDBYTES_DU
#endif

/* mlkem/params.h */
#if defined(MLKEM_ETA2)
#undef MLKEM_ETA2
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
#if defined(MLKEM_INDCPA_BYTES)
#undef MLKEM_INDCPA_BYTES
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
#if defined(MLKEM_INDCCA_CIPHERTEXTBYTES)
#undef MLKEM_INDCCA_CIPHERTEXTBYTES
#endif

/* mlkem/params.h */
#if defined(KECCAK_WAY)
#undef KECCAK_WAY
#endif

/* mlkem/poly.h */
#if defined(POLY_H)
#undef POLY_H
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
#if defined(poly)
#undef poly
#endif

/* mlkem/poly.h */
#if defined(poly_mulcache)
#undef poly_mulcache
#endif

/* mlkem/poly.h */
#if defined(scalar_compress_d1)
#undef scalar_compress_d1
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
#if defined(scalar_compress_d10)
#undef scalar_compress_d10
#endif

/* mlkem/poly.h */
#if defined(scalar_compress_d11)
#undef scalar_compress_d11
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
#if defined(scalar_decompress_d10)
#undef scalar_decompress_d10
#endif

/* mlkem/poly.h */
#if defined(scalar_decompress_d11)
#undef scalar_decompress_d11
#endif

/* mlkem/poly.h */
#if defined(scalar_signed_to_unsigned_q)
#undef scalar_signed_to_unsigned_q
#endif

/* mlkem/poly.h */
#if defined(poly_compress_du)
#undef poly_compress_du
#endif

/* mlkem/poly.h */
#if defined(poly_decompress_du)
#undef poly_decompress_du
#endif

/* mlkem/poly.h */
#if defined(poly_compress_dv)
#undef poly_compress_dv
#endif

/* mlkem/poly.h */
#if defined(poly_decompress_dv)
#undef poly_decompress_dv
#endif

/* mlkem/poly.h */
#if defined(poly_tobytes)
#undef poly_tobytes
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
#if defined(poly_tomsg)
#undef poly_tomsg
#endif

/* mlkem/poly.h */
#if defined(poly_getnoise_eta1_4x)
#undef poly_getnoise_eta1_4x
#endif

/* mlkem/poly.h */
#if defined(poly_getnoise_eta2_4x)
#undef poly_getnoise_eta2_4x
#endif

/* mlkem/poly.h */
#if defined(poly_getnoise_eta2)
#undef poly_getnoise_eta2
#endif

/* mlkem/poly.h */
#if defined(poly_getnoise_eta1122_4x)
#undef poly_getnoise_eta1122_4x
#endif

/* mlkem/poly.h */
#if defined(poly_basemul_montgomery_cached)
#undef poly_basemul_montgomery_cached
#endif

/* mlkem/poly.h */
#if defined(poly_tomont)
#undef poly_tomont
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
#if defined(poly_add)
#undef poly_add
#endif

/* mlkem/poly.h */
#if defined(poly_sub)
#undef poly_sub
#endif

/* mlkem/polyvec.h */
#if defined(POLYVEC_H)
#undef POLYVEC_H
#endif

/* mlkem/polyvec.h */
#if defined(polyvec)
#undef polyvec
#endif

/* mlkem/polyvec.h */
#if defined(polyvec_mulcache)
#undef polyvec_mulcache
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
#if defined(polyvec_tobytes)
#undef polyvec_tobytes
#endif

/* mlkem/polyvec.h */
#if defined(polyvec_frombytes)
#undef polyvec_frombytes
#endif

/* mlkem/polyvec.h */
#if defined(polyvec_ntt)
#undef polyvec_ntt
#endif

/* mlkem/polyvec.h */
#if defined(polyvec_invntt_tomont)
#undef polyvec_invntt_tomont
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
#if defined(polyvec_mulcache_compute)
#undef polyvec_mulcache_compute
#endif

/* mlkem/polyvec.h */
#if defined(polyvec_reduce)
#undef polyvec_reduce
#endif

/* mlkem/polyvec.h */
#if defined(polyvec_add)
#undef polyvec_add
#endif

/* mlkem/polyvec.h */
#if defined(polyvec_tomont)
#undef polyvec_tomont
#endif

/* mlkem/randombytes.h */
#if defined(RANDOMBYTES_H)
#undef RANDOMBYTES_H
#endif

/* mlkem/reduce.h */
#if defined(REDUCE_H)
#undef REDUCE_H
#endif

/* mlkem/reduce.h */
#if defined(cast_uint16_to_int16)
#undef cast_uint16_to_int16
#endif

/* mlkem/reduce.h */
#if defined(montgomery_reduce_generic)
#undef montgomery_reduce_generic
#endif

/* mlkem/reduce.h */
#if defined(montgomery_reduce)
#undef montgomery_reduce
#endif

/* mlkem/reduce.h */
#if defined(fqmul)
#undef fqmul
#endif

/* mlkem/reduce.h */
#if defined(barrett_reduce)
#undef barrett_reduce
#endif

/* mlkem/reduce.h */
#if defined(HALF_Q)
#undef HALF_Q
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
#if defined(rej_uniform)
#undef rej_uniform
#endif

/* mlkem/symmetric.h */
#if defined(SYMMETRIC_H)
#undef SYMMETRIC_H
#endif

/* mlkem/symmetric.h */
#if defined(hash_h)
#undef hash_h
#endif

/* mlkem/symmetric.h */
#if defined(hash_g)
#undef hash_g
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
#if defined(prf_eta2)
#undef prf_eta2
#endif

/* mlkem/symmetric.h */
#if defined(prf_eta1_x4)
#undef prf_eta1_x4
#endif

/* mlkem/symmetric.h */
#if defined(xof_ctx)
#undef xof_ctx
#endif

/* mlkem/symmetric.h */
#if defined(xof_x4_ctx)
#undef xof_x4_ctx
#endif

/* mlkem/symmetric.h */
#if defined(xof_absorb)
#undef xof_absorb
#endif

/* mlkem/symmetric.h */
#if defined(xof_squeezeblocks)
#undef xof_squeezeblocks
#endif

/* mlkem/symmetric.h */
#if defined(xof_release)
#undef xof_release
#endif

/* mlkem/symmetric.h */
#if defined(xof_x4_absorb)
#undef xof_x4_absorb
#endif

/* mlkem/symmetric.h */
#if defined(xof_x4_squeezeblocks)
#undef xof_x4_squeezeblocks
#endif

/* mlkem/symmetric.h */
#if defined(xof_x4_release)
#undef xof_x4_release
#endif

/* mlkem/symmetric.h */
#if defined(XOF_RATE)
#undef XOF_RATE
#endif

/* mlkem/sys.h */
#if defined(MLKEM_NATIVE_SYS_H)
#undef MLKEM_NATIVE_SYS_H
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
#if defined(SYS_X86_64)
#undef SYS_X86_64
#endif

/* mlkem/sys.h */
#if defined(SYS_X86_64_AVX2)
#undef SYS_X86_64_AVX2
#endif

/* mlkem/sys.h */
#if defined(SYS_LITTLE_ENDIAN)
#undef SYS_LITTLE_ENDIAN
#endif

/* mlkem/sys.h */
#if defined(SYS_BIG_ENDIAN)
#undef SYS_BIG_ENDIAN
#endif

/* mlkem/sys.h */
#if defined(INLINE)
#undef INLINE
#endif

/* mlkem/sys.h */
#if defined(ALWAYS_INLINE)
#undef ALWAYS_INLINE
#endif

/* mlkem/sys.h */
#if defined(INLINE)
#undef INLINE
#endif

/* mlkem/sys.h */
#if defined(ALWAYS_INLINE)
#undef ALWAYS_INLINE
#endif

/* mlkem/sys.h */
#if defined(INLINE)
#undef INLINE
#endif

/* mlkem/sys.h */
#if defined(ALWAYS_INLINE)
#undef ALWAYS_INLINE
#endif

/* mlkem/sys.h */
#if defined(INLINE)
#undef INLINE
#endif

/* mlkem/sys.h */
#if defined(ALWAYS_INLINE)
#undef ALWAYS_INLINE
#endif

/* mlkem/sys.h */
#if defined(RESTRICT)
#undef RESTRICT
#endif

/* mlkem/sys.h */
#if defined(RESTRICT)
#undef RESTRICT
#endif

/* mlkem/sys.h */
#if defined(RESTRICT)
#undef RESTRICT
#endif

/* mlkem/sys.h */
#if defined(DEFAULT_ALIGN)
#undef DEFAULT_ALIGN
#endif

/* mlkem/sys.h */
#if defined(ALIGN)
#undef ALIGN
#endif

/* mlkem/sys.h */
#if defined(asm)
#undef asm
#endif

/* mlkem/sys.h */
#if defined(asm)
#undef asm
#endif

/* mlkem/sys.h */
#if defined(ALIGN)
#undef ALIGN
#endif

/* mlkem/verify.c */
#if defined(empty_cu_verify)
#undef empty_cu_verify
#endif

/* mlkem/verify.h */
#if defined(VERIFY_H)
#undef VERIFY_H
#endif

/* mlkem/verify.h */
#if defined(value_barrier_u8)
#undef value_barrier_u8
#endif

/* mlkem/verify.h */
#if defined(value_barrier_u32)
#undef value_barrier_u32
#endif

/* mlkem/verify.h */
#if defined(value_barrier_i32)
#undef value_barrier_i32
#endif

/* mlkem/verify.h */
#if defined(ct_cmask_neg_i16)
#undef ct_cmask_neg_i16
#endif

/* mlkem/verify.h */
#if defined(ct_cmask_nonzero_u8)
#undef ct_cmask_nonzero_u8
#endif

/* mlkem/verify.h */
#if defined(ct_cmask_nonzero_u16)
#undef ct_cmask_nonzero_u16
#endif

/* mlkem/verify.h */
#if defined(ct_sel_uint8)
#undef ct_sel_uint8
#endif

/* mlkem/verify.h */
#if defined(ct_sel_int16)
#undef ct_sel_int16
#endif

/* mlkem/verify.h */
#if defined(ct_memcmp)
#undef ct_memcmp
#endif

/* mlkem/verify.h */
#if defined(ct_cmov_zero)
#undef ct_cmov_zero
#endif

/* mlkem/verify.h */
#if defined(MLKEM_USE_ASM_VALUE_BARRIER)
#undef MLKEM_USE_ASM_VALUE_BARRIER
#endif

/* mlkem/verify.h */
#if defined(ct_opt_blocker_u64)
#undef ct_opt_blocker_u64
#endif


#if !defined(MLKEM_NATIVE_MONOBUILD_KEEP_FIPS202_HEADERS)

/*
 * Undo all #define directives from *.c or *.h files
 */

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
#if defined(SHAKE128_RATE)
#undef SHAKE128_RATE
#endif

/* mlkem/fips202/fips202.h */
#if defined(SHAKE256_RATE)
#undef SHAKE256_RATE
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
#if defined(SHA3_512_RATE)
#undef SHA3_512_RATE
#endif

/* mlkem/fips202/fips202.h */
#if defined(shake128ctx)
#undef shake128ctx
#endif

/* mlkem/fips202/fips202.h */
#if defined(shake128_absorb_once)
#undef shake128_absorb_once
#endif

/* mlkem/fips202/fips202.h */
#if defined(shake128_squeezeblocks)
#undef shake128_squeezeblocks
#endif

/* mlkem/fips202/fips202.h */
#if defined(shake128_release)
#undef shake128_release
#endif

/* mlkem/fips202/fips202.h */
#if defined(shake256)
#undef shake256
#endif

/* mlkem/fips202/fips202.h */
#if defined(SHA3_256_HASHBYTES)
#undef SHA3_256_HASHBYTES
#endif

/* mlkem/fips202/fips202.h */
#if defined(sha3_256)
#undef sha3_256
#endif

/* mlkem/fips202/fips202.h */
#if defined(SHA3_512_HASHBYTES)
#undef SHA3_512_HASHBYTES
#endif

/* mlkem/fips202/fips202.h */
#if defined(sha3_512)
#undef sha3_512
#endif

/* mlkem/fips202/fips202_backend.h */
#if defined(MLKEM_NATIVE_FIPS202_IMPL_H)
#undef MLKEM_NATIVE_FIPS202_IMPL_H
#endif

/* mlkem/fips202/fips202x4.c */
#if defined(shake256x4_ctx)
#undef shake256x4_ctx
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
#if defined(shake256x4_squeezeblocks)
#undef shake256x4_squeezeblocks
#endif

/* mlkem/fips202/fips202x4.h */
#if defined(FIPS_202X4_H)
#undef FIPS_202X4_H
#endif

/* mlkem/fips202/fips202x4.h */
#if defined(shake128x4ctx)
#undef shake128x4ctx
#endif

/* mlkem/fips202/fips202x4.h */
#if defined(shake128x4_absorb_once)
#undef shake128x4_absorb_once
#endif

/* mlkem/fips202/fips202x4.h */
#if defined(shake128x4_squeezeblocks)
#undef shake128x4_squeezeblocks
#endif

/* mlkem/fips202/fips202x4.h */
#if defined(shake128x4_release)
#undef shake128x4_release
#endif

/* mlkem/fips202/fips202x4.h */
#if defined(shake256x4)
#undef shake256x4
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
#if defined(KeccakF_RoundConstants)
#undef KeccakF_RoundConstants
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
#if defined(KeccakF1600_StateXORBytes)
#undef KeccakF1600_StateXORBytes
#endif

/* mlkem/fips202/keccakf1600.h */
#if defined(KeccakF1600x4_StateExtractBytes)
#undef KeccakF1600x4_StateExtractBytes
#endif

/* mlkem/fips202/keccakf1600.h */
#if defined(KeccakF1600x4_StateXORBytes)
#undef KeccakF1600x4_StateXORBytes
#endif

/* mlkem/fips202/keccakf1600.h */
#if defined(KeccakF1600x4_StatePermute)
#undef KeccakF1600x4_StatePermute
#endif

/* mlkem/fips202/keccakf1600.h */
#if defined(KeccakF1600_StatePermute)
#undef KeccakF1600_StatePermute
#endif

/* mlkem/fips202/keccakf1600.h */
#if defined(KeccakF1600_StatePermute)
#undef KeccakF1600_StatePermute
#endif

/* mlkem/fips202/native/aarch64/cortex_a55.h */
#if defined(FIPS202_NATIVE_PROFILE_H)
#undef FIPS202_NATIVE_PROFILE_H
#endif

/* mlkem/fips202/native/aarch64/cortex_a55.h */
#if defined(MLKEM_NATIVE_FIPS202_BACKEND_AARCH64_A55)
#undef MLKEM_NATIVE_FIPS202_BACKEND_AARCH64_A55
#endif

/* mlkem/fips202/native/aarch64/cortex_a55.h */
#if defined(MLKEM_NATIVE_FIPS202_BACKEND_NAME)
#undef MLKEM_NATIVE_FIPS202_BACKEND_NAME
#endif

/* mlkem/fips202/native/aarch64/cortex_a55.h */
#if defined(MLKEM_NATIVE_FIPS202_BACKEND_IMPL)
#undef MLKEM_NATIVE_FIPS202_BACKEND_IMPL
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
#if defined(MLKEM_NATIVE_FIPS202_BACKEND_NAME)
#undef MLKEM_NATIVE_FIPS202_BACKEND_NAME
#endif

/* mlkem/fips202/native/aarch64/default.h */
#if defined(MLKEM_NATIVE_FIPS202_BACKEND_IMPL)
#undef MLKEM_NATIVE_FIPS202_BACKEND_IMPL
#endif

/* mlkem/fips202/native/aarch64/src/cortex_a55_impl.h */
#if defined(FIPS202_NATIVE_PROFILE_IMPL_H)
#undef FIPS202_NATIVE_PROFILE_IMPL_H
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
#if defined(MLKEM_USE_FIPS202_X1_NATIVE)
#undef MLKEM_USE_FIPS202_X1_NATIVE
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

/* mlkem/fips202/native/aarch64/src/default_impl.h */
#if defined(MLKEM_USE_FIPS202_X4_NATIVE)
#undef MLKEM_USE_FIPS202_X4_NATIVE
#endif

/* mlkem/fips202/native/aarch64/src/fips202_native_aarch64.h */
#if defined(FIPS202_AARCH64_NATIVE_H)
#undef FIPS202_AARCH64_NATIVE_H
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
#if defined(keccak_f1600_x4_scalar_v8a_asm_hybrid_opt)
#undef keccak_f1600_x4_scalar_v8a_asm_hybrid_opt
#endif

/* mlkem/fips202/native/aarch64/src/fips202_native_aarch64.h */
#if defined(keccak_f1600_x4_scalar_v84a_asm_hybrid_opt)
#undef keccak_f1600_x4_scalar_v84a_asm_hybrid_opt
#endif

/* mlkem/fips202/native/aarch64/src/fips202_native_aarch64.h */
#if defined(keccak_f1600_x4_scalar_v8a_v84a_hybrid_asm_opt)
#undef keccak_f1600_x4_scalar_v8a_v84a_hybrid_asm_opt
#endif

/* mlkem/fips202/native/aarch64/src/fips202_native_aarch64.h */
#if defined(keccakf1600_round_constants)
#undef keccakf1600_round_constants
#endif

/* mlkem/fips202/native/aarch64/src/keccakf1600_round_constants.c */
#if defined(empty_cu_keccakf1600_round_constants)
#undef empty_cu_keccakf1600_round_constants
#endif

/* mlkem/fips202/native/api.h */
#if defined(MLKEM_NATIVE_FIPS202_NATIVE_API_H)
#undef MLKEM_NATIVE_FIPS202_NATIVE_API_H
#endif

/* mlkem/fips202/native/default.h */
#if defined(MLKEM_NATIVE_FIPS202_BACKEND_DEFAULT_H)
#undef MLKEM_NATIVE_FIPS202_BACKEND_DEFAULT_H
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
#if defined(ROL64in256_8)
#undef ROL64in256_8
#endif

/* mlkem/fips202/native/x86_64/src/KeccakP-1600-times4-SIMD256.c */
#if defined(ROL64in256_56)
#undef ROL64in256_56
#endif

/* mlkem/fips202/native/x86_64/src/KeccakP-1600-times4-SIMD256.c */
#if defined(STORE256)
#undef STORE256
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
#if defined(SnP_laneLengthInBytes)
#undef SnP_laneLengthInBytes
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
#if defined(thetaRhoPiChiIotaPrepareTheta)
#undef thetaRhoPiChiIotaPrepareTheta
#endif

/* mlkem/fips202/native/x86_64/src/KeccakP-1600-times4-SIMD256.c */
#if defined(thetaRhoPiChiIota)
#undef thetaRhoPiChiIota
#endif

/* mlkem/fips202/native/x86_64/src/KeccakP-1600-times4-SIMD256.c */
#if defined(copyFromState)
#undef copyFromState
#endif

/* mlkem/fips202/native/x86_64/src/KeccakP-1600-times4-SIMD256.c */
#if defined(SCATTER_STORE256)
#undef SCATTER_STORE256
#endif

/* mlkem/fips202/native/x86_64/src/KeccakP-1600-times4-SIMD256.c */
#if defined(copyToState)
#undef copyToState
#endif

/* mlkem/fips202/native/x86_64/src/KeccakP-1600-times4-SIMD256.c */
#if defined(copyStateVariables)
#undef copyStateVariables
#endif

/* mlkem/fips202/native/x86_64/src/KeccakP-1600-times4-SIMD256.c */
#if defined(FullUnrolling)
#undef FullUnrolling
#endif

/* mlkem/fips202/native/x86_64/src/KeccakP-1600-times4-SIMD256.c */
#if defined(Unrolling)
#undef Unrolling
#endif

/* mlkem/fips202/native/x86_64/src/KeccakP-1600-times4-SIMD256.c */
#if defined(empty_cu_avx2_keccakx4)
#undef empty_cu_avx2_keccakx4
#endif

/* mlkem/fips202/native/x86_64/src/KeccakP-1600-times4-SnP.h */
#if defined(_KeccakP_1600_times4_SnP_h_)
#undef _KeccakP_1600_times4_SnP_h_
#endif

/* mlkem/fips202/native/x86_64/src/KeccakP-1600-times4-SnP.h */
#if defined(KeccakP1600times4_statesAlignment)
#undef KeccakP1600times4_statesAlignment
#endif

/* mlkem/fips202/native/x86_64/src/KeccakP-1600-times4-SnP.h */
#if defined(KeccakP1600times4_PermuteAll_24rounds)
#undef KeccakP1600times4_PermuteAll_24rounds
#endif

/* mlkem/fips202/native/x86_64/src/KeccakP-SIMD256-config.h */
#if defined(KeccakP1600times4_implementation_config)
#undef KeccakP1600times4_implementation_config
#endif

/* mlkem/fips202/native/x86_64/src/KeccakP-SIMD256-config.h */
#if defined(KeccakP1600times4_fullUnrolling)
#undef KeccakP1600times4_fullUnrolling
#endif

/* mlkem/fips202/native/x86_64/src/KeccakP-SIMD256-config.h */
#if defined(KeccakP1600times4_useAVX2)
#undef KeccakP1600times4_useAVX2
#endif

/* mlkem/fips202/native/x86_64/src/KeccakP-align.h */
#if defined(_keccakp_align_h_)
#undef _keccakp_align_h_
#endif

/* mlkem/fips202/native/x86_64/src/KeccakP-align.h */
#if defined(ALIGN)
#undef ALIGN
#endif

/* mlkem/fips202/native/x86_64/src/KeccakP-align.h */
#if defined(ALIGN)
#undef ALIGN
#endif

/* mlkem/fips202/native/x86_64/src/KeccakP-align.h */
#if defined(ALIGN)
#undef ALIGN
#endif

/* mlkem/fips202/native/x86_64/src/KeccakP-align.h */
#if defined(ALIGN)
#undef ALIGN
#endif

/* mlkem/fips202/native/x86_64/src/KeccakP-brg_endian.h */
#if defined(_KECCAKP_BRG_ENDIAN_H)
#undef _KECCAKP_BRG_ENDIAN_H
#endif

/* mlkem/fips202/native/x86_64/src/KeccakP-brg_endian.h */
#if defined(IS_BIG_ENDIAN)
#undef IS_BIG_ENDIAN
#endif

/* mlkem/fips202/native/x86_64/src/KeccakP-brg_endian.h */
#if defined(IS_LITTLE_ENDIAN)
#undef IS_LITTLE_ENDIAN
#endif

/* mlkem/fips202/native/x86_64/src/KeccakP-brg_endian.h */
#if defined(PLATFORM_BYTE_ORDER)
#undef PLATFORM_BYTE_ORDER
#endif

/* mlkem/fips202/native/x86_64/src/KeccakP-brg_endian.h */
#if defined(PLATFORM_BYTE_ORDER)
#undef PLATFORM_BYTE_ORDER
#endif

/* mlkem/fips202/native/x86_64/src/KeccakP-brg_endian.h */
#if defined(PLATFORM_BYTE_ORDER)
#undef PLATFORM_BYTE_ORDER
#endif

/* mlkem/fips202/native/x86_64/src/KeccakP-brg_endian.h */
#if defined(PLATFORM_BYTE_ORDER)
#undef PLATFORM_BYTE_ORDER
#endif

/* mlkem/fips202/native/x86_64/src/KeccakP-brg_endian.h */
#if defined(PLATFORM_BYTE_ORDER)
#undef PLATFORM_BYTE_ORDER
#endif

/* mlkem/fips202/native/x86_64/src/KeccakP-brg_endian.h */
#if defined(PLATFORM_BYTE_ORDER)
#undef PLATFORM_BYTE_ORDER
#endif

/* mlkem/fips202/native/x86_64/src/KeccakP-brg_endian.h */
#if defined(PLATFORM_BYTE_ORDER)
#undef PLATFORM_BYTE_ORDER
#endif

/* mlkem/fips202/native/x86_64/src/KeccakP-brg_endian.h */
#if defined(PLATFORM_BYTE_ORDER)
#undef PLATFORM_BYTE_ORDER
#endif

/* mlkem/fips202/native/x86_64/src/KeccakP-brg_endian.h */
#if defined(PLATFORM_BYTE_ORDER)
#undef PLATFORM_BYTE_ORDER
#endif

/* mlkem/fips202/native/x86_64/src/KeccakP-brg_endian.h */
#if defined(PLATFORM_BYTE_ORDER)
#undef PLATFORM_BYTE_ORDER
#endif

/* mlkem/fips202/native/x86_64/src/KeccakP-brg_endian.h */
#if defined(PLATFORM_BYTE_ORDER)
#undef PLATFORM_BYTE_ORDER
#endif

/* mlkem/fips202/native/x86_64/src/KeccakP-brg_endian.h */
#if defined(PLATFORM_BYTE_ORDER)
#undef PLATFORM_BYTE_ORDER
#endif

/* mlkem/fips202/native/x86_64/src/KeccakP-brg_endian.h */
#if defined(PLATFORM_BYTE_ORDER)
#undef PLATFORM_BYTE_ORDER
#endif

/* mlkem/fips202/native/x86_64/src/KeccakP-brg_endian.h */
#if defined(PLATFORM_BYTE_ORDER)
#undef PLATFORM_BYTE_ORDER
#endif

/* mlkem/fips202/native/x86_64/src/KeccakP-brg_endian.h */
#if defined(PLATFORM_BYTE_ORDER)
#undef PLATFORM_BYTE_ORDER
#endif

/* mlkem/fips202/native/x86_64/src/KeccakP-brg_endian.h */
#if defined(PLATFORM_BYTE_ORDER)
#undef PLATFORM_BYTE_ORDER
#endif

/* mlkem/fips202/native/x86_64/src/KeccakP-brg_endian.h */
#if defined(PLATFORM_BYTE_ORDER)
#undef PLATFORM_BYTE_ORDER
#endif

/* mlkem/fips202/native/x86_64/src/KeccakP-brg_endian.h */
#if defined(PLATFORM_BYTE_ORDER)
#undef PLATFORM_BYTE_ORDER
#endif

/* mlkem/fips202/native/x86_64/src/KeccakP-brg_endian.h */
#if defined(PLATFORM_BYTE_ORDER)
#undef PLATFORM_BYTE_ORDER
#endif

/* mlkem/fips202/native/x86_64/src/KeccakP-brg_endian.h */
#if defined(PLATFORM_BYTE_ORDER)
#undef PLATFORM_BYTE_ORDER
#endif

/* mlkem/fips202/native/x86_64/src/KeccakP-brg_endian.h */
#if defined(PLATFORM_BYTE_ORDER)
#undef PLATFORM_BYTE_ORDER
#endif

/* mlkem/fips202/native/x86_64/src/KeccakP-brg_endian.h */
#if defined(PLATFORM_BYTE_ORDER)
#undef PLATFORM_BYTE_ORDER
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
#if defined(MLKEM_NATIVE_FIPS202_PROFILE_H)
#undef MLKEM_NATIVE_FIPS202_PROFILE_H
#endif

/* mlkem/fips202/native/x86_64/xkcp.h */
#if defined(MLKEM_NATIVE_FIPS202_BACKEND_X86_64_XKCP)
#undef MLKEM_NATIVE_FIPS202_BACKEND_X86_64_XKCP
#endif

/* mlkem/fips202/native/x86_64/xkcp.h */
#if defined(MLKEM_NATIVE_FIPS202_BACKEND_NAME)
#undef MLKEM_NATIVE_FIPS202_BACKEND_NAME
#endif

/* mlkem/fips202/native/x86_64/xkcp.h */
#if defined(MLKEM_NATIVE_FIPS202_BACKEND_IMPL)
#undef MLKEM_NATIVE_FIPS202_BACKEND_IMPL
#endif

#endif /* MLKEM_NATIVE_MONOBUILD_KEEP_FIPS202_HEADERS */
