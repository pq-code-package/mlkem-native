/*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */

/*
 * WARNING: This file is auto-generated from scripts/autogen
 *          Do not modify it directly.
 */

/*
 * Monolithic compilation unit bundling all compilation units within
 * mlkem-native
 */

/******************************************************************************
 *
 * Single compilation unit (SCU) for fixed-level build of mlkem-native
 *
 * This compilation unit bundles together all source files for a build
 * of mlkem-native for a fixed security level (MLKEM-512/768/1024).
 *
 * # API
 *
 * The API exposed by this file is described in mlkem_native.h.
 *
 * # Multi-level build
 *
 * If you want an SCU build of mlkem-native with support for multiple security
 * levels, you need to include this file multiple times, and set
 * MLK_CONFIG_MULTILEVEL_WITH_SHARED and MLK_CONFIG_MULTILEVEL_NO_SHARED
 * appropriately. This is exemplified in examples/monolithic_build_multilevel.
 *
 * # Configuration
 *
 * - MLK_CONFIG_MONOBUILD_CUSTOM_FIPS202
 *   Set this option if you use a custom FIPS202 implementation.
 *
 * - MLK_CONFIG_MONOBUILD_WITH_NATIVE_ARITH
 *   Set this option if you want to include the native arithmetic backends
 *   in your build.
 *
 * - MLK_CONFIG_MONOBUILD_WITH_NATIVE_FIPS202
 *   Set this option if you want to include the native FIPS202 backends
 *   in your build.
 *
 * - MLK_CONFIG_MONOBUILD_KEEP_SHARED_HEADERS
 *   Set this option if you want to keep the directives defined in
 *   level-independent headers. This is needed for a multi-level build.
 */

/* If parts of the mlkem-native source tree are not used,
 * consider reducing this header via `unifdef`.
 *
 * Example:
 * ```bash
 * unifdef -UMLK_CONFIG_MONOBUILD_WITH_NATIVE_ARITH mlkem_native_monobuild.c
 * ```
 */

#include "mlkem/sys.h"

#include "mlkem/compress.c"
#include "mlkem/debug.c"
#include "mlkem/indcpa.c"
#include "mlkem/kem.c"
#include "mlkem/poly.c"
#include "mlkem/poly_k.c"
#include "mlkem/sampling.c"
#include "mlkem/verify.c"

#if !defined(MLK_CONFIG_MONOBUILD_CUSTOM_FIPS202)
#include "mlkem/fips202/fips202.c"
#include "mlkem/fips202/fips202x4.c"
#include "mlkem/fips202/keccakf1600.c"
#endif

#if defined(MLK_CONFIG_MONOBUILD_WITH_NATIVE_ARITH)
#if defined(MLK_SYS_AARCH64)
#include "mlkem/native/aarch64/src/aarch64_zetas.c"
#include "mlkem/native/aarch64/src/rej_uniform_table.c"
#endif
#if defined(MLK_SYS_X86_64)
#include "mlkem/native/x86_64/src/basemul.c"
#include "mlkem/native/x86_64/src/compress_avx2.c"
#include "mlkem/native/x86_64/src/consts.c"
#include "mlkem/native/x86_64/src/rej_uniform_avx2.c"
#include "mlkem/native/x86_64/src/rej_uniform_table.c"
#endif /* MLK_SYS_X86_64 */
#endif /* MLK_CONFIG_MONOBUILD_WITH_NATIVE_ARITH */

#if defined(MLK_CONFIG_MONOBUILD_WITH_NATIVE_FIPS202)
#if defined(MLK_SYS_AARCH64)
#include "mlkem/fips202/native/aarch64/src/keccakf1600_round_constants.c"
#endif
#if defined(MLK_SYS_X86_64)
#include "mlkem/fips202/native/x86_64/src/KeccakP_1600_times4_SIMD256.c"
#endif
#endif /* MLK_CONFIG_MONOBUILD_WITH_NATIVE_FIPS202 */

/*
 * Undefine macros from MLK_CONFIG_PARAMETER_SET-specific files
 */
/* mlkem/common.h */
#undef MLK_ADD_PARAM_SET
#undef MLK_ASM_FN_SYMBOL
#undef MLK_ASM_NAMESPACE
#undef MLK_COMMON_H
#undef MLK_CONCAT
#undef MLK_CONCAT_
#undef MLK_CONFIG_API_NAMESPACE_PREFIX
#undef MLK_CONFIG_API_PARAMETER_SET
#undef MLK_EMPTY_CU
#undef MLK_EXTERNAL_API
#undef MLK_FIPS202X4_HEADER_FILE
#undef MLK_FIPS202_HEADER_FILE
#undef MLK_INTERNAL_API
#undef MLK_MULTILEVEL_BUILD
#undef MLK_NAMESPACE
#undef MLK_NAMESPACE_K
#undef MLK_NAMESPACE_PREFIX
#undef MLK_NAMESPACE_PREFIX_K
/* mlkem/indcpa.h */
#undef MLK_INDCPA_H
#undef mlk_gen_matrix
#undef mlk_indcpa_dec
#undef mlk_indcpa_enc
#undef mlk_indcpa_keypair_derand
#undef mlk_indcpa_marshal_pk
#undef mlk_indcpa_marshal_sk
#undef mlk_indcpa_parse_pk
#undef mlk_indcpa_parse_sk
#undef mlk_indcpa_public_key
#undef mlk_indcpa_secret_key
/* mlkem/kem.h */
#undef MLK_CONFIG_API_NO_SUPERCOP
#undef MLK_KEM_H
#undef crypto_kem_dec
#undef crypto_kem_dec_struct
#undef crypto_kem_enc
#undef crypto_kem_enc_derand
#undef crypto_kem_enc_derand_struct
#undef crypto_kem_enc_struct
#undef crypto_kem_keypair
#undef crypto_kem_keypair_derand
#undef crypto_kem_keypair_derand_struct
#undef crypto_kem_keypair_struct
#undef crypto_kem_marshal_pk
#undef crypto_kem_marshal_sk
#undef crypto_kem_parse_pk
#undef crypto_kem_parse_sk
#undef crypto_kem_pk_from_sk
#undef crypto_kem_sk_from_seed
#undef mlk_public_key
#undef mlk_secret_key
/* mlkem/mlkem_native.h */
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
#undef MLKEM_PUBLICKEYBYTES
#undef MLKEM_PUBLICKEYBYTES_
#undef MLKEM_SECRETKEYBYTES
#undef MLKEM_SECRETKEYBYTES_
#undef MLKEM_SYMBYTES
#undef MLK_API_CONCAT
#undef MLK_API_CONCAT_
#undef MLK_API_CONCAT_UNDERSCORE
#undef MLK_API_MUST_CHECK_RETURN_VALUE
#undef MLK_API_NAMESPACE
#undef MLK_H
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
#undef MLKEM_K
#undef MLKEM_N
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
#undef MLKEM_UINT12_LIMIT
#undef MLK_PARAMS_H
/* mlkem/poly_k.h */
#undef MLK_POLY_K_H
#undef mlk_poly_compress_du
#undef mlk_poly_compress_dv
#undef mlk_poly_decompress_du
#undef mlk_poly_decompress_dv
#undef mlk_poly_getnoise_eta1122_4x
#undef mlk_poly_getnoise_eta1_4x
#undef mlk_poly_getnoise_eta2
#undef mlk_poly_getnoise_eta2_4x
#undef mlk_polymat
#undef mlk_polyvec
#undef mlk_polyvec_add
#undef mlk_polyvec_basemul_acc_montgomery_cached
#undef mlk_polyvec_compress_du
#undef mlk_polyvec_decompress_du
#undef mlk_polyvec_frombytes
#undef mlk_polyvec_invntt_tomont
#undef mlk_polyvec_mulcache
#undef mlk_polyvec_mulcache_compute
#undef mlk_polyvec_ntt
#undef mlk_polyvec_reduce
#undef mlk_polyvec_tobytes
#undef mlk_polyvec_tomont
/* mlkem/sys.h */
#undef MLK_ALIGN
#undef MLK_ALIGN_UP
#undef MLK_ALWAYS_INLINE
#undef MLK_CET_ENDBR
#undef MLK_CT_TESTING_DECLASSIFY
#undef MLK_CT_TESTING_SECRET
#undef MLK_DEFAULT_ALIGN
#undef MLK_HAVE_INLINE_ASM
#undef MLK_INLINE
#undef MLK_MUST_CHECK_RETURN_VALUE
#undef MLK_RESTRICT
#undef MLK_SYS_AARCH64
#undef MLK_SYS_AARCH64_EB
#undef MLK_SYS_BIG_ENDIAN
#undef MLK_SYS_H
#undef MLK_SYS_LITTLE_ENDIAN
#undef MLK_SYS_PPC64LE
#undef MLK_SYS_RISCV64
#undef MLK_SYS_WINDOWS
#undef MLK_SYS_X86_64
#undef MLK_SYS_X86_64_AVX2

#if !defined(MLK_CONFIG_MONOBUILD_KEEP_SHARED_HEADERS)
/*
 * Undefine macros from MLK_CONFIG_PARAMETER_SET-generic files
 */
/* mlkem/compress.h */
#undef MLK_COMPRESS_H
#undef mlk_poly_compress_d10
#undef mlk_poly_compress_d11
#undef mlk_poly_compress_d4
#undef mlk_poly_compress_d5
#undef mlk_poly_decompress_d10
#undef mlk_poly_decompress_d11
#undef mlk_poly_decompress_d4
#undef mlk_poly_decompress_d5
#undef mlk_poly_frombytes
#undef mlk_poly_frommsg
#undef mlk_poly_tobytes
#undef mlk_poly_tomsg
/* mlkem/debug.h */
#undef MLK_DEBUG_H
#undef mlk_assert
#undef mlk_assert_abs_bound
#undef mlk_assert_abs_bound_2d
#undef mlk_assert_bound
#undef mlk_assert_bound_2d
#undef mlk_debug_check_assert
#undef mlk_debug_check_bounds
/* mlkem/poly.h */
#undef MLK_INVNTT_BOUND
#undef MLK_NTT_BOUND
#undef MLK_POLY_H
#undef mlk_poly_add
#undef mlk_poly_invntt_tomont
#undef mlk_poly_mulcache_compute
#undef mlk_poly_ntt
#undef mlk_poly_reduce
#undef mlk_poly_sub
#undef mlk_poly_tomont
/* mlkem/randombytes.h */
#undef MLK_RANDOMBYTES_H
/* mlkem/sampling.h */
#undef MLK_SAMPLING_H
#undef mlk_poly_cbd2
#undef mlk_poly_cbd3
#undef mlk_poly_rej_uniform
#undef mlk_poly_rej_uniform_x4
/* mlkem/symmetric.h */
#undef MLK_SYMMETRIC_H
#undef MLK_XOF_RATE
#undef mlk_hash_g
#undef mlk_hash_h
#undef mlk_hash_j
#undef mlk_prf_eta
#undef mlk_prf_eta1
#undef mlk_prf_eta1_x4
#undef mlk_prf_eta2
#undef mlk_xof_absorb
#undef mlk_xof_ctx
#undef mlk_xof_init
#undef mlk_xof_release
#undef mlk_xof_squeezeblocks
#undef mlk_xof_x4_absorb
#undef mlk_xof_x4_ctx
#undef mlk_xof_x4_init
#undef mlk_xof_x4_release
#undef mlk_xof_x4_squeezeblocks
/* mlkem/verify.h */
#undef MLK_USE_ASM_VALUE_BARRIER
#undef MLK_VERIFY_H
#undef mlk_ct_opt_blocker_u64
/* mlkem/cbmc.h */
#undef MLK_CBMC_H
#undef __contract__
#undef __loop__

#if !defined(MLK_CONFIG_MONOBUILD_CUSTOM_FIPS202)
/*
 * Undefine macros from FIPS-202 files
 */
/* mlkem/fips202/fips202.h */
#undef FIPS202_X4_DEFAULT_IMPLEMENTATION
#undef MLK_FIPS202_FIPS202_H
#undef SHA3_256_HASHBYTES
#undef SHA3_256_RATE
#undef SHA3_384_RATE
#undef SHA3_512_HASHBYTES
#undef SHA3_512_RATE
#undef SHAKE128_RATE
#undef SHAKE256_RATE
#undef mlk_sha3_256
#undef mlk_sha3_512
#undef mlk_shake128_absorb_once
#undef mlk_shake128_init
#undef mlk_shake128_release
#undef mlk_shake128_squeezeblocks
#undef mlk_shake256
/* mlkem/fips202/fips202x4.h */
#undef MLK_FIPS202_FIPS202X4_H
#undef mlk_shake128x4_absorb_once
#undef mlk_shake128x4_init
#undef mlk_shake128x4_release
#undef mlk_shake128x4_squeezeblocks
#undef mlk_shake256x4
/* mlkem/fips202/keccakf1600.h */
#undef MLK_FIPS202_KECCAKF1600_H
#undef MLK_KECCAK_LANES
#undef MLK_KECCAK_WAY
#undef mlk_keccakf1600_extract_bytes
#undef mlk_keccakf1600_permute
#undef mlk_keccakf1600_xor_bytes
#undef mlk_keccakf1600x4_extract_bytes
#undef mlk_keccakf1600x4_permute
#undef mlk_keccakf1600x4_xor_bytes
#endif /* !MLK_CONFIG_MONOBUILD_CUSTOM_FIPS202 */

#if defined(MLK_CONFIG_MONOBUILD_WITH_NATIVE_FIPS202)
/*
 * Undefine macros from native code
 */
/* mlkem/fips202/native/aarch64/auto.h */
#undef MLK_FIPS202_NATIVE_AARCH64_AUTO_H
/* mlkem/fips202/native/aarch64/src/fips202_native_aarch64.h */
#undef MLK_FIPS202_NATIVE_AARCH64_SRC_FIPS202_NATIVE_AARCH64_H
#undef mlk_keccak_f1600_x1_scalar_asm
#undef mlk_keccak_f1600_x1_v84a_asm
#undef mlk_keccak_f1600_x2_v84a_asm
#undef mlk_keccak_f1600_x2_v8a_v84a_asm_hybrid
#undef mlk_keccak_f1600_x4_scalar_v84a_asm_hybrid
#undef mlk_keccak_f1600_x4_scalar_v8a_asm_hybrid
#undef mlk_keccak_f1600_x4_scalar_v8a_v84a_hybrid_asm
#undef mlk_keccakf1600_round_constants
/* mlkem/fips202/native/aarch64/x1_scalar.h */
#undef MLK_FIPS202_AARCH64_NEED_X1_SCALAR
#undef MLK_FIPS202_NATIVE_AARCH64_X1_SCALAR_H
#undef MLK_USE_FIPS202_X1_NATIVE
/* mlkem/fips202/native/aarch64/x1_v84a.h */
#undef MLK_FIPS202_AARCH64_NEED_X1_V84A
#undef MLK_FIPS202_NATIVE_AARCH64_X1_V84A_H
#undef MLK_USE_FIPS202_X1_NATIVE
/* mlkem/fips202/native/aarch64/x2_v84a.h */
#undef MLK_FIPS202_AARCH64_NEED_X2_V84A
#undef MLK_FIPS202_NATIVE_AARCH64_X2_V84A_H
#undef MLK_USE_FIPS202_X2_NATIVE
/* mlkem/fips202/native/aarch64/x4_v8a_scalar.h */
#undef MLK_FIPS202_AARCH64_NEED_X4_V8A_SCALAR_HYBRID
#undef MLK_FIPS202_NATIVE_AARCH64_X4_V8A_SCALAR_H
#undef MLK_USE_FIPS202_X4_NATIVE
/* mlkem/fips202/native/aarch64/x4_v8a_v84a_scalar.h */
#undef MLK_FIPS202_AARCH64_NEED_X4_V8A_V84A_SCALAR_HYBRID
#undef MLK_FIPS202_NATIVE_AARCH64_X4_V8A_V84A_SCALAR_H
#undef MLK_USE_FIPS202_X4_NATIVE
/* mlkem/fips202/native/api.h */
#undef MLK_FIPS202_NATIVE_API_H
/* mlkem/fips202/native/auto.h */
#undef MLK_FIPS202_NATIVE_AUTO_H
/* mlkem/fips202/native/x86_64/src/KeccakP_1600_times4_SIMD256.h */
#undef MLK_FIPS202_NATIVE_X86_64_SRC_KECCAKP_1600_TIMES4_SIMD256_H
#undef mlk_keccakf1600x4_permute24
/* mlkem/fips202/native/x86_64/xkcp.h */
#undef MLK_FIPS202_NATIVE_X86_64_XKCP_H
#undef MLK_FIPS202_X86_64_XKCP
#undef MLK_USE_FIPS202_X4_NATIVE
#endif /* MLK_CONFIG_MONOBUILD_WITH_NATIVE_FIPS202 */
#if defined(MLK_CONFIG_MONOBUILD_WITH_NATIVE_ARITH)
/*
 * Undefine macros from native code
 */
/* mlkem/native/aarch64/meta.h */
#undef MLK_ARITH_BACKEND_AARCH64
#undef MLK_NATIVE_AARCH64_META_H
#undef MLK_USE_NATIVE_INTT
#undef MLK_USE_NATIVE_NTT
#undef MLK_USE_NATIVE_POLYVEC_BASEMUL_ACC_MONTGOMERY_CACHED
#undef MLK_USE_NATIVE_POLY_MULCACHE_COMPUTE
#undef MLK_USE_NATIVE_POLY_REDUCE
#undef MLK_USE_NATIVE_POLY_TOBYTES
#undef MLK_USE_NATIVE_POLY_TOMONT
#undef MLK_USE_NATIVE_REJ_UNIFORM
/* mlkem/native/aarch64/src/arith_native_aarch64.h */
#undef MLK_NATIVE_AARCH64_SRC_ARITH_NATIVE_AARCH64_H
#undef mlk_aarch64_invntt_zetas_layer12345
#undef mlk_aarch64_invntt_zetas_layer67
#undef mlk_aarch64_ntt_zetas_layer12345
#undef mlk_aarch64_ntt_zetas_layer67
#undef mlk_aarch64_zetas_mulcache_native
#undef mlk_aarch64_zetas_mulcache_twisted_native
#undef mlk_intt_asm
#undef mlk_ntt_asm
#undef mlk_poly_mulcache_compute_asm
#undef mlk_poly_reduce_asm
#undef mlk_poly_tobytes_asm
#undef mlk_poly_tomont_asm
#undef mlk_polyvec_basemul_acc_montgomery_cached_asm_k2
#undef mlk_polyvec_basemul_acc_montgomery_cached_asm_k3
#undef mlk_polyvec_basemul_acc_montgomery_cached_asm_k4
#undef mlk_rej_uniform_asm
#undef mlk_rej_uniform_table
/* mlkem/native/aarch64/src/consts.h */
#undef MLK_NATIVE_AARCH64_SRC_CONSTS_H
#undef mlk_zetas_mulcache_native
#undef mlk_zetas_mulcache_twisted_native
/* mlkem/native/api.h */
#undef MLK_INVNTT_BOUND
#undef MLK_NATIVE_API_H
#undef MLK_NTT_BOUND
/* mlkem/native/meta.h */
#undef MLK_NATIVE_META_H
/* mlkem/native/x86_64/meta.h */
#undef MLK_ARITH_BACKEND_X86_64_DEFAULT
#undef MLK_NATIVE_X86_64_META_H
#undef MLK_USE_NATIVE_INTT
#undef MLK_USE_NATIVE_NTT
#undef MLK_USE_NATIVE_NTT_CUSTOM_ORDER
#undef MLK_USE_NATIVE_POLYVEC_BASEMUL_ACC_MONTGOMERY_CACHED
#undef MLK_USE_NATIVE_POLY_COMPRESS_D10
#undef MLK_USE_NATIVE_POLY_COMPRESS_D11
#undef MLK_USE_NATIVE_POLY_COMPRESS_D4
#undef MLK_USE_NATIVE_POLY_COMPRESS_D5
#undef MLK_USE_NATIVE_POLY_DECOMPRESS_D10
#undef MLK_USE_NATIVE_POLY_DECOMPRESS_D11
#undef MLK_USE_NATIVE_POLY_DECOMPRESS_D4
#undef MLK_USE_NATIVE_POLY_DECOMPRESS_D5
#undef MLK_USE_NATIVE_POLY_FROMBYTES
#undef MLK_USE_NATIVE_POLY_MULCACHE_COMPUTE
#undef MLK_USE_NATIVE_POLY_REDUCE
#undef MLK_USE_NATIVE_POLY_TOBYTES
#undef MLK_USE_NATIVE_POLY_TOMONT
#undef MLK_USE_NATIVE_REJ_UNIFORM
/* mlkem/native/x86_64/src/align.h */
#undef MLK_ALIGNED_INT16
#undef MLK_NATIVE_X86_64_SRC_ALIGN_H
/* mlkem/native/x86_64/src/arith_native_x86_64.h */
#undef MLK_AVX2_REJ_UNIFORM_BUFLEN
#undef MLK_NATIVE_X86_64_SRC_ARITH_NATIVE_X86_64_H
#undef mlk_basemul_avx2
#undef mlk_invntt_avx2
#undef mlk_ntt_avx2
#undef mlk_nttfrombytes_avx2
#undef mlk_nttpack_avx2
#undef mlk_ntttobytes_avx2
#undef mlk_nttunpack_avx2
#undef mlk_poly_compress_d10_avx2
#undef mlk_poly_compress_d11_avx2
#undef mlk_poly_compress_d4_avx2
#undef mlk_poly_compress_d5_avx2
#undef mlk_poly_decompress_d10_avx2
#undef mlk_poly_decompress_d11_avx2
#undef mlk_poly_decompress_d4_avx2
#undef mlk_poly_decompress_d5_avx2
#undef mlk_polyvec_basemul_acc_montgomery_cached_avx2
#undef mlk_reduce_avx2
#undef mlk_rej_uniform_avx2
#undef mlk_rej_uniform_table
#undef mlk_tomont_avx2
/* mlkem/native/x86_64/src/consts.h */
#undef MLK_AVX2_BACKEND_DATA_OFFSET_16XFHI
#undef MLK_AVX2_BACKEND_DATA_OFFSET_16XFLO
#undef MLK_AVX2_BACKEND_DATA_OFFSET_16XMASK
#undef MLK_AVX2_BACKEND_DATA_OFFSET_16XMONTSQHI
#undef MLK_AVX2_BACKEND_DATA_OFFSET_16XMONTSQLO
#undef MLK_AVX2_BACKEND_DATA_OFFSET_16XQ
#undef MLK_AVX2_BACKEND_DATA_OFFSET_16XQINV
#undef MLK_AVX2_BACKEND_DATA_OFFSET_16XSHIFT
#undef MLK_AVX2_BACKEND_DATA_OFFSET_16XV
#undef MLK_AVX2_BACKEND_DATA_OFFSET_REVIDXB
#undef MLK_AVX2_BACKEND_DATA_OFFSET_REVIDXD
#undef MLK_AVX2_BACKEND_DATA_OFFSET_ZETAS_EXP
#undef MLK_NATIVE_X86_64_SRC_CONSTS_H
#undef mlk_qdata
#endif /* MLK_CONFIG_MONOBUILD_WITH_NATIVE_ARITH */
#endif /* !MLK_CONFIG_MONOBUILD_KEEP_SHARED_HEADERS */
