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

/* If parts of the mlkem-native source tree are not used,
 * consider reducing this header via `unifdef`.
 *
 * Example:
 * ```bash
 * unifdef -UMLK_MONOBUILD_WITH_NATIVE_ARITH mlkem_native_monobuild.c
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
#include "mlkem/zetas.c"

#if !defined(MLK_MONOBUILD_CUSTOM_FIPS202)
#include "mlkem/fips202/fips202.c"
#include "mlkem/fips202/fips202x4.c"
#include "mlkem/fips202/keccakf1600.c"
#endif /* !MLK_MONOBUILD_CUSTOM_FIPS202 */

#if defined(MLK_MONOBUILD_WITH_NATIVE_ARITH)
#if defined(MLK_SYS_AARCH64)
#include "mlkem/native/aarch64/src/aarch64_zetas.c"
#include "mlkem/native/aarch64/src/rej_uniform_table.c"
#endif /* MLK_SYS_AARCH64 */
#if defined(MLK_SYS_X86_64)
#include "mlkem/native/x86_64/src/basemul.c"
#include "mlkem/native/x86_64/src/compress_avx2.c"
#include "mlkem/native/x86_64/src/consts.c"
#include "mlkem/native/x86_64/src/rej_uniform_avx2.c"
#include "mlkem/native/x86_64/src/rej_uniform_table.c"
#endif /* MLK_SYS_X86_64 */
#endif /* MLK_MONOBUILD_WITH_NATIVE_ARITH */

#if defined(MLK_MONOBUILD_WITH_NATIVE_FIPS202)
#if defined(MLK_SYS_AARCH64)
#include "mlkem/fips202/native/aarch64/src/keccakf1600_round_constants.c"
#endif /* MLK_SYS_AARCH64 */
#if defined(MLK_SYS_X86_64)
#include "mlkem/fips202/native/x86_64/src/KeccakP-1600-times4-SIMD256.c"
#endif /* MLK_SYS_X86_64 */
#endif /* MLK_MONOBUILD_WITH_NATIVE_FIPS202 */

/*
 * Undefine macros from MLKEM_K-specific files
 */
/* mlkem/common.h */
#undef MLK_ARITH_BACKEND_NAME
#undef MLK_ASM_FN_SYMBOL
#undef MLK_ASM_NAMESPACE
#undef MLK_COMMON_H
#undef MLK_EMPTY_CU
#undef MLK_FIPS202X4_HEADER_FILE
#undef MLK_FIPS202_BACKEND_NAME
#undef MLK_FIPS202_HEADER_FILE
#undef MLK_INTERNAL_API
#undef MLK_MAKE_NAMESPACE
#undef MLK_MAKE_NAMESPACE_
#undef MLK_MAKE_NAMESPACE_K
#undef MLK_MAKE_NAMESPACE_K_
#undef MLK_NAMESPACE
#undef MLK_NAMESPACE_K
#undef MLK_PREFIX_UNDERSCORE
#undef MLK_PREFIX_UNDERSCORE_
/* mlkem/config.h */
#undef MLKEM_K
#undef MLK_ARITH_BACKEND_FILE
#undef MLK_CONFIG_H
#undef MLK_DEFAULT_NAMESPACE_PREFIX
#undef MLK_FIPS202_BACKEND_FILE
#undef MLK_NAMESPACE_PREFIX
/* mlkem/indcpa.h */
#undef MLK_INDCPA_H
#undef gen_matrix
#undef indcpa_dec
#undef indcpa_enc
#undef indcpa_keypair_derand
/* mlkem/kem.h */
#undef MLK_KEM_H
#undef crypto_kem_dec
#undef crypto_kem_enc
#undef crypto_kem_enc_derand
#undef crypto_kem_keypair
#undef crypto_kem_keypair_derand
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
#undef MLK_BUILD_INFO_CONCAT2
#undef MLK_BUILD_INFO_CONCAT2_
#undef MLK_BUILD_INFO_CONCAT3
#undef MLK_BUILD_INFO_CONCAT3_
#undef MLK_BUILD_INFO_LVL
#undef MLK_BUILD_INFO_NAMESPACE
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
#undef MLKEM_LVL
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

#if !defined(MLK_MONOBUILD_KEEP_SHARED_HEADERS)
/*
 * Undefine macros from MLKEM_K-generic files
 */
/* mlkem/arith_backend.h */
#undef MLK_ARITH_BACKEND_H
/* mlkem/compress.h */
#undef MLK_COMPRESS_H
#undef poly_compress_d10
#undef poly_compress_d11
#undef poly_compress_d4
#undef poly_compress_d5
#undef poly_decompress_d10
#undef poly_decompress_d11
#undef poly_decompress_d4
#undef poly_decompress_d5
#undef poly_frombytes
#undef poly_frommsg
#undef poly_tobytes
#undef poly_tomsg
#undef scalar_compress_d1
#undef scalar_compress_d10
#undef scalar_compress_d11
#undef scalar_compress_d4
#undef scalar_compress_d5
#undef scalar_decompress_d10
#undef scalar_decompress_d11
#undef scalar_decompress_d4
#undef scalar_decompress_d5
/* mlkem/debug.h */
#undef MLK_DEBUG_H
#undef debug_assert
#undef debug_assert_abs_bound
#undef debug_assert_abs_bound_2d
#undef debug_assert_bound
#undef debug_assert_bound_2d
#undef mlkem_debug_assert
#undef mlkem_debug_check_bounds
/* mlkem/poly.h */
#undef MLK_INVNTT_BOUND
#undef MLK_NTT_BOUND
#undef MLK_POLY_H
#undef cast_uint16_to_int16
#undef montgomery_reduce
#undef poly
#undef poly_add
#undef poly_invntt_tomont
#undef poly_mulcache
#undef poly_mulcache_compute
#undef poly_ntt
#undef poly_reduce
#undef poly_sub
#undef poly_tomont
#undef zetas
/* mlkem/randombytes.h */
#undef MLK_RANDOMBYTES_H
/* mlkem/sampling.h */
#undef MLK_SAMPLING_H
#undef poly_cbd2
#undef poly_cbd3
#undef poly_rej_uniform
#undef poly_rej_uniform_x4
/* mlkem/symmetric.h */
#undef MLK_SYMMETRIC_H
#undef XOF_RATE
#undef hash_g
#undef hash_h
#undef hash_j
#undef prf_eta
#undef prf_eta1
#undef prf_eta1_x4
#undef prf_eta2
#undef xof_absorb
#undef xof_ctx
#undef xof_init
#undef xof_release
#undef xof_squeezeblocks
#undef xof_x4_absorb
#undef xof_x4_ctx
#undef xof_x4_init
#undef xof_x4_release
#undef xof_x4_squeezeblocks
/* mlkem/sys.h */
#undef MLK_ALIGN
#undef MLK_ALWAYS_INLINE
#undef MLK_CET_ENDBR
#undef MLK_DEFAULT_ALIGN
#undef MLK_INLINE
#undef MLK_RESTRICT
#undef MLK_SYS_AARCH64
#undef MLK_SYS_AARCH64_EB
#undef MLK_SYS_BIG_ENDIAN
#undef MLK_SYS_H
#undef MLK_SYS_LITTLE_ENDIAN
#undef MLK_SYS_X86_64
#undef MLK_SYS_X86_64_AVX2
/* mlkem/verify.h */
#undef MLK_USE_ASM_VALUE_BARRIER
#undef MLK_VERIFY_H
#undef ct_cmask_neg_i16
#undef ct_cmask_nonzero_u16
#undef ct_cmask_nonzero_u8
#undef ct_cmov_zero
#undef ct_memcmp
#undef ct_opt_blocker_u64
#undef ct_sel_int16
#undef ct_sel_uint8
#undef value_barrier_i32
#undef value_barrier_u32
#undef value_barrier_u8
/* mlkem/cbmc.h */
#undef MLK_CBMC_H
#undef __contract__
#undef __loop__

#if !defined(MLK_MONOBUILD_CUSTOM_FIPS202)
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
#undef sha3_256
#undef sha3_512
#undef shake128_absorb_once
#undef shake128_init
#undef shake128_release
#undef shake128_squeezeblocks
#undef shake128ctx
#undef shake256
/* mlkem/fips202/fips202_backend.h */
#undef MLK_FIPS202_FIPS202_BACKEND_H
/* mlkem/fips202/fips202x4.h */
#undef MLK_FIPS202_FIPS202X4_H
#undef shake128x4_absorb_once
#undef shake128x4_init
#undef shake128x4_release
#undef shake128x4_squeezeblocks
#undef shake128x4ctx
#undef shake256x4
/* mlkem/fips202/keccakf1600.h */
#undef KECCAK_LANES
#undef KECCAK_WAY
#undef KeccakF1600_StateExtractBytes
#undef KeccakF1600_StatePermute
#undef KeccakF1600_StateXORBytes
#undef KeccakF1600x4_StateExtractBytes
#undef KeccakF1600x4_StatePermute
#undef KeccakF1600x4_StateXORBytes
#undef MLK_FIPS202_KECCAKF1600_H
#endif /* !MLK_MONOBUILD_CUSTOM_FIPS202 */

#if defined(MLK_MONOBUILD_WITH_NATIVE_FIPS202)
/*
 * Undefine macros from native code
 */
/* mlkem/fips202/native/aarch64/meta.h */
#undef MLK_FIPS202_BACKEND_AARCH64_DEFAULT
#undef MLK_FIPS202_BACKEND_IMPL
#undef MLK_FIPS202_BACKEND_NAME
#undef MLK_FIPS202_NATIVE_AARCH64_META_H
#undef MLK_FIPS202_NATIVE_PROFILE_H
/* mlkem/fips202/native/aarch64/meta_cortex_a55.h */
#undef MLK_FIPS202_BACKEND_AARCH64_A55
#undef MLK_FIPS202_BACKEND_IMPL
#undef MLK_FIPS202_BACKEND_NAME
#undef MLK_FIPS202_NATIVE_AARCH64_META_CORTEX_A55_H
#undef MLK_FIPS202_NATIVE_PROFILE_H
/* mlkem/fips202/native/aarch64/src/cortex_a55_impl.h */
#undef MLK_FIPS202_NATIVE_AARCH64_SRC_CORTEX_A55_IMPL_H
#undef MLK_FIPS202_NATIVE_PROFILE_IMPL_H
#undef MLK_USE_FIPS202_X1_NATIVE
/* mlkem/fips202/native/aarch64/src/default_impl.h */
#undef MLK_FIPS202_NATIVE_AARCH64_SRC_DEFAULT_IMPL_H
#undef MLK_FIPS202_NATIVE_PROFILE_IMPL_H
#undef MLK_USE_FIPS202_X1_NATIVE
#undef MLK_USE_FIPS202_X2_NATIVE
#undef MLK_USE_FIPS202_X4_NATIVE
/* mlkem/fips202/native/aarch64/src/fips202_native_aarch64.h */
#undef MLK_FIPS202_NATIVE_AARCH64_SRC_FIPS202_NATIVE_AARCH64_H
#undef keccak_f1600_x1_scalar_asm_opt
#undef keccak_f1600_x1_v84a_asm_clean
#undef keccak_f1600_x2_v84a_asm_clean
#undef keccak_f1600_x2_v8a_v84a_asm_hybrid
#undef keccak_f1600_x4_scalar_v84a_asm_hybrid_opt
#undef keccak_f1600_x4_scalar_v8a_asm_hybrid_opt
#undef keccak_f1600_x4_scalar_v8a_v84a_hybrid_asm_opt
#undef keccakf1600_round_constants
/* mlkem/fips202/native/api.h */
#undef MLK_FIPS202_NATIVE_API_H
/* mlkem/fips202/native/meta.h */
#undef MLK_FIPS202_NATIVE_META_H
/* mlkem/fips202/native/x86_64/meta.h */
#undef MLK_FIPS202_BACKEND_IMPL
#undef MLK_FIPS202_BACKEND_NAME
#undef MLK_FIPS202_BACKEND_X86_64_XKCP
#undef MLK_FIPS202_NATIVE_X86_64_META_H
#undef MLK_FIPS202_PROFILE_H
/* mlkem/fips202/native/x86_64/src/xkcp_impl.h */
#undef KeccakP1600times4_PermuteAll_24rounds
#undef MLK_FIPS202_NATIVE_X86_64_SRC_XKCP_IMPL_H
#undef MLK_FIPS202_PROFILE_IMPL_H
#undef MLK_USE_FIPS202_X4_NATIVE
#endif /* MLK_MONOBUILD_WITH_NATIVE_FIPS202 */
#if defined(MLK_MONOBUILD_WITH_NATIVE_ARITH)
/*
 * Undefine macros from native code
 */
/* mlkem/native/aarch64/meta.h */
#undef MLK_ARITH_BACKEND_AARCH64_OPT
#undef MLK_ARITH_BACKEND_IMPL
#undef MLK_ARITH_BACKEND_NAME
#undef MLK_ARITH_PROFILE_H
#undef MLK_NATIVE_AARCH64_META_H
/* mlkem/native/aarch64/src/arith_native_aarch64.h */
#undef MLK_NATIVE_AARCH64_SRC_ARITH_NATIVE_AARCH64_H
#undef aarch64_invntt_zetas_layer01234
#undef aarch64_invntt_zetas_layer56
#undef aarch64_ntt_zetas_layer01234
#undef aarch64_ntt_zetas_layer56
#undef aarch64_zetas_mulcache_native
#undef aarch64_zetas_mulcache_twisted_native
#undef intt_asm_opt
#undef ntt_asm_opt
#undef poly_mulcache_compute_asm_opt
#undef poly_reduce_asm_opt
#undef poly_tobytes_asm_opt
#undef poly_tomont_asm_opt
#undef polyvec_basemul_acc_montgomery_cached_asm_k2_opt
#undef polyvec_basemul_acc_montgomery_cached_asm_k3_opt
#undef polyvec_basemul_acc_montgomery_cached_asm_k4_opt
#undef rej_uniform_asm_clean
#undef rej_uniform_table
/* mlkem/native/aarch64/src/consts.h */
#undef MLK_NATIVE_AARCH64_SRC_CONSTS_H
#undef zetas_mulcache_native
#undef zetas_mulcache_twisted_native
/* mlkem/native/aarch64/src/opt_impl.h */
#undef MLK_ARITH_PROFILE_IMPL_H
#undef MLK_NATIVE_AARCH64_SRC_OPT_IMPL_H
#undef MLK_USE_NATIVE_INTT
#undef MLK_USE_NATIVE_NTT
#undef MLK_USE_NATIVE_POLYVEC_BASEMUL_ACC_MONTGOMERY_CACHED
#undef MLK_USE_NATIVE_POLY_MULCACHE_COMPUTE
#undef MLK_USE_NATIVE_POLY_REDUCE
#undef MLK_USE_NATIVE_POLY_TOBYTES
#undef MLK_USE_NATIVE_POLY_TOMONT
#undef MLK_USE_NATIVE_REJ_UNIFORM
/* mlkem/native/api.h */
#undef MLK_INVNTT_BOUND
#undef MLK_NATIVE_API_H
#undef MLK_NTT_BOUND
/* mlkem/native/meta.h */
#undef MLK_NATIVE_META_H
/* mlkem/native/x86_64/meta.h */
#undef MLK_ARITH_BACKEND_IMPL
#undef MLK_ARITH_BACKEND_NAME
#undef MLK_ARITH_BACKEND_X86_64_DEFAULT
#undef MLK_ARITH_PROFILE_H
#undef MLK_NATIVE_X86_64_META_H
/* mlkem/native/x86_64/src/align.h */
#undef MLK_ALIGNED_INT16
#undef MLK_NATIVE_X86_64_SRC_ALIGN_H
/* mlkem/native/x86_64/src/arith_native_x86_64.h */
#undef MLK_AVX2_REJ_UNIFORM_BUFLEN
#undef MLK_NATIVE_X86_64_SRC_ARITH_NATIVE_X86_64_H
#undef basemul_avx2
#undef invntt_avx2
#undef ntt_avx2
#undef nttfrombytes_avx2
#undef nttpack_avx2
#undef ntttobytes_avx2
#undef nttunpack_avx2
#undef poly_compress_d10_avx2
#undef poly_compress_d11_avx2
#undef poly_compress_d4_avx2
#undef poly_compress_d5_avx2
#undef poly_decompress_d10_avx2
#undef poly_decompress_d11_avx2
#undef poly_decompress_d4_avx2
#undef poly_decompress_d5_avx2
#undef polyvec_basemul_acc_montgomery_cached_avx2
#undef reduce_avx2
#undef rej_uniform_avx2
#undef rej_uniform_table
#undef tomont_avx2
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
#undef qdata
/* mlkem/native/x86_64/src/default_impl.h */
#undef MLK_ARITH_PROFILE_IMPL_H
#undef MLK_NATIVE_X86_64_SRC_DEFAULT_IMPL_H
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
#endif /* MLK_MONOBUILD_WITH_NATIVE_ARITH */
#endif /* MLK_MONOBUILD_KEEP_SHARED_HEADERS */
