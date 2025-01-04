/*
 * Copyright (c) 2024 The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0
 */

/*
 * WARNING: This file is auto-generated from scripts/autogenerate_files.py
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
#include "mlkem/fips202/native/aarch64/src/keccakf1600_round_constants.c"
#include "mlkem/fips202/native/x86_64/src/KeccakP-1600-times4-SIMD256.c"
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

/*
 * Undo all #define directives from *.c or *.h files
 */

/* mlkem/arith_backend.h:6 */
#if defined(MLKEM_NATIVE_ARITH_IMPL_H)
#undef MLKEM_NATIVE_ARITH_IMPL_H
#endif

/* mlkem/cbd.h:5 */
#if defined(CBD_H)
#undef CBD_H
#endif

/* mlkem/cbd.h:11 */
#if defined(poly_cbd_eta1)
#undef poly_cbd_eta1
#endif

/* mlkem/cbd.h:30 */
#if defined(poly_cbd_eta2)
#undef poly_cbd_eta2
#endif

/* mlkem/cbmc.h:13 */
#if defined(STATIC_INLINE_TESTABLE)
#undef STATIC_INLINE_TESTABLE
#endif

/* mlkem/cbmc.h:14 */
#if defined(STATIC_TESTABLE)
#undef STATIC_TESTABLE
#endif

/* mlkem/cbmc.h:16 */
#if defined(__contract__)
#undef __contract__
#endif

/* mlkem/cbmc.h:17 */
#if defined(__loop__)
#undef __loop__
#endif

/* mlkem/cbmc.h:18 */
#if defined(cassert)
#undef cassert
#endif

/* mlkem/cbmc.h:23 */
#if defined(STATIC_TESTABLE)
#undef STATIC_TESTABLE
#endif

/* mlkem/cbmc.h:24 */
#if defined(STATIC_INLINE_TESTABLE)
#undef STATIC_INLINE_TESTABLE
#endif

/* mlkem/cbmc.h:26 */
#if defined(__contract__)
#undef __contract__
#endif

/* mlkem/cbmc.h:27 */
#if defined(__loop__)
#undef __loop__
#endif

/* mlkem/cbmc.h:30 */
#if defined(assigns)
#undef assigns
#endif

/* mlkem/cbmc.h:33 */
#if defined(requires)
#undef requires
#endif

/* mlkem/cbmc.h:34 */
#if defined(ensures)
#undef ensures
#endif

/* mlkem/cbmc.h:36 */
#if defined(invariant)
#undef invariant
#endif

/* mlkem/cbmc.h:37 */
#if defined(decreases)
#undef decreases
#endif

/* mlkem/cbmc.h:39 */
#if defined(cassert)
#undef cassert
#endif

/* mlkem/cbmc.h:40 */
#if defined(assume)
#undef assume
#endif

/* mlkem/cbmc.h:51 */
#if defined(return_value)
#undef return_value
#endif

/* mlkem/cbmc.h:57 */
#if defined(object_whole)
#undef object_whole
#endif

/* mlkem/cbmc.h:58 */
#if defined(memory_slice)
#undef memory_slice
#endif

/* mlkem/cbmc.h:59 */
#if defined(same_object)
#undef same_object
#endif

/* mlkem/cbmc.h:65 */
#if defined(memory_no_alias)
#undef memory_no_alias
#endif

/* mlkem/cbmc.h:66 */
#if defined(readable)
#undef readable
#endif

/* mlkem/cbmc.h:67 */
#if defined(writeable)
#undef writeable
#endif

/* mlkem/cbmc.h:73 */
#if defined(old)
#undef old
#endif

/* mlkem/cbmc.h:74 */
#if defined(loop_entry)
#undef loop_entry
#endif

/* mlkem/cbmc.h:86 */
#if defined(forall)
#undef forall
#endif

/* mlkem/cbmc.h:93 */
#if defined(EXISTS)
#undef EXISTS
#endif

/* mlkem/cbmc.h:119 */
#if defined(CBMC_CONCAT_)
#undef CBMC_CONCAT_
#endif

/* mlkem/cbmc.h:120 */
#if defined(CBMC_CONCAT)
#undef CBMC_CONCAT
#endif

/* mlkem/cbmc.h:122 */
#if defined(array_bound_core)
#undef array_bound_core
#endif

/* mlkem/cbmc.h:132 */
#if defined(array_bound)
#undef array_bound
#endif

/* mlkem/cbmc.h:138 */
#if defined(array_abs_bound)
#undef array_abs_bound
#endif

/* mlkem/common.h:5 */
#if defined(MLKEM_NATIVE_COMMON_H)
#undef MLKEM_NATIVE_COMMON_H
#endif

/* mlkem/common.h:32 */
#if defined(MLKEM_ASM_NAMESPACE)
#undef MLKEM_ASM_NAMESPACE
#endif

/* mlkem/common.h:33 */
#if defined(FIPS202_ASM_NAMESPACE)
#undef FIPS202_ASM_NAMESPACE
#endif

/* mlkem/common.h:35 */
#if defined(_PREFIX_UNDERSCORE)
#undef _PREFIX_UNDERSCORE
#endif

/* mlkem/common.h:36 */
#if defined(PREFIX_UNDERSCORE)
#undef PREFIX_UNDERSCORE
#endif

/* mlkem/common.h:37 */
#if defined(MLKEM_ASM_NAMESPACE)
#undef MLKEM_ASM_NAMESPACE
#endif

/* mlkem/common.h:38 */
#if defined(FIPS202_ASM_NAMESPACE)
#undef FIPS202_ASM_NAMESPACE
#endif

/* mlkem/config.h:6 */
#if defined(MLKEM_NATIVE_CONFIG_H)
#undef MLKEM_NATIVE_CONFIG_H
#endif

/* mlkem/config.h:20 */
#if defined(MLKEM_K)
#undef MLKEM_K
#endif

/* mlkem/config.h:45 */
#if defined(MLKEM_NAMESPACE)
#undef MLKEM_NAMESPACE
#endif

/* mlkem/config.h:53 */
#if defined(FIPS202_NAMESPACE)
#undef FIPS202_NAMESPACE
#endif

/* mlkem/config.h:80 */
#if defined(MLKEM_NATIVE_ARITH_BACKEND)
#undef MLKEM_NATIVE_ARITH_BACKEND
#endif

/* mlkem/config.h:94 */
#if defined(MLKEM_NATIVE_FIPS202_BACKEND)
#undef MLKEM_NATIVE_FIPS202_BACKEND
#endif

/* mlkem/debug/debug.c:4 */
#if defined(_ISOC99_SOURCE)
#undef _ISOC99_SOURCE
#endif

/* mlkem/debug/debug.c:55 */
#if defined(empty_cu_debug)
#undef empty_cu_debug
#endif

/* mlkem/debug/debug.h:5 */
#if defined(MLKEM_DEBUG_H)
#undef MLKEM_DEBUG_H
#endif

/* mlkem/debug/debug.h:62 */
#if defined(CASSERT)
#undef CASSERT
#endif

/* mlkem/debug/debug.h:72 */
#if defined(SCALAR_BOUND)
#undef SCALAR_BOUND
#endif

/* mlkem/debug/debug.h:82 */
#if defined(UBOUND)
#undef UBOUND
#endif

/* mlkem/debug/debug.h:94 */
#if defined(BOUND)
#undef BOUND
#endif

/* mlkem/debug/debug.h:105 */
#if defined(POLY_BOUND_MSG)
#undef POLY_BOUND_MSG
#endif

/* mlkem/debug/debug.h:113 */
#if defined(POLY_UBOUND_MSG)
#undef POLY_UBOUND_MSG
#endif

/* mlkem/debug/debug.h:120 */
#if defined(POLY_BOUND)
#undef POLY_BOUND
#endif

/* mlkem/debug/debug.h:127 */
#if defined(POLY_UBOUND)
#undef POLY_UBOUND
#endif

/* mlkem/debug/debug.h:133 */
#if defined(POLYVEC_BOUND)
#undef POLYVEC_BOUND
#endif

/* mlkem/debug/debug.h:147 */
#if defined(POLYVEC_UBOUND)
#undef POLYVEC_UBOUND
#endif

/* mlkem/debug/debug.h:157 */
#if defined(MLKEM_CONCAT_)
#undef MLKEM_CONCAT_
#endif

/* mlkem/debug/debug.h:158 */
#if defined(MLKEM_CONCAT)
#undef MLKEM_CONCAT
#endif

/* mlkem/debug/debug.h:161 */
#if defined(MLKEM_STATIC_ASSERT_DEFINE)
#undef MLKEM_STATIC_ASSERT_DEFINE
#endif

/* mlkem/debug/debug.h:167 */
#if defined(MLKEM_STATIC_ASSERT_ADD_LINE0)
#undef MLKEM_STATIC_ASSERT_ADD_LINE0
#endif

/* mlkem/debug/debug.h:169 */
#if defined(MLKEM_STATIC_ASSERT_ADD_LINE1)
#undef MLKEM_STATIC_ASSERT_ADD_LINE1
#endif

/* mlkem/debug/debug.h:171 */
#if defined(MLKEM_STATIC_ASSERT_ADD_LINE2)
#undef MLKEM_STATIC_ASSERT_ADD_LINE2
#endif

/* mlkem/debug/debug.h:173 */
#if defined(MLKEM_STATIC_ASSERT_ADD_ERROR)
#undef MLKEM_STATIC_ASSERT_ADD_ERROR
#endif

/* mlkem/debug/debug.h:175 */
#if defined(STATIC_ASSERT)
#undef STATIC_ASSERT
#endif

/* mlkem/debug/debug.h:179 */
#if defined(CASSERT)
#undef CASSERT
#endif

/* mlkem/debug/debug.h:183 */
#if defined(SCALAR_BOUND)
#undef SCALAR_BOUND
#endif

/* mlkem/debug/debug.h:187 */
#if defined(BOUND)
#undef BOUND
#endif

/* mlkem/debug/debug.h:191 */
#if defined(POLY_BOUND)
#undef POLY_BOUND
#endif

/* mlkem/debug/debug.h:195 */
#if defined(POLYVEC_BOUND)
#undef POLYVEC_BOUND
#endif

/* mlkem/debug/debug.h:199 */
#if defined(POLY_BOUND_MSG)
#undef POLY_BOUND_MSG
#endif

/* mlkem/debug/debug.h:203 */
#if defined(UBOUND)
#undef UBOUND
#endif

/* mlkem/debug/debug.h:207 */
#if defined(POLY_UBOUND)
#undef POLY_UBOUND
#endif

/* mlkem/debug/debug.h:211 */
#if defined(POLYVEC_UBOUND)
#undef POLYVEC_UBOUND
#endif

/* mlkem/debug/debug.h:215 */
#if defined(POLY_UBOUND_MSG)
#undef POLY_UBOUND_MSG
#endif

/* mlkem/debug/debug.h:219 */
#if defined(STATIC_ASSERT)
#undef STATIC_ASSERT
#endif

/* mlkem/fips202/fips202.c:177 */
#if defined(shake256ctx)
#undef shake256ctx
#endif

/* mlkem/fips202/fips202.h:5 */
#if defined(FIPS202_H)
#undef FIPS202_H
#endif

/* mlkem/fips202/fips202.h:12 */
#if defined(SHAKE128_RATE)
#undef SHAKE128_RATE
#endif

/* mlkem/fips202/fips202.h:13 */
#if defined(SHAKE256_RATE)
#undef SHAKE256_RATE
#endif

/* mlkem/fips202/fips202.h:14 */
#if defined(SHA3_256_RATE)
#undef SHA3_256_RATE
#endif

/* mlkem/fips202/fips202.h:15 */
#if defined(SHA3_384_RATE)
#undef SHA3_384_RATE
#endif

/* mlkem/fips202/fips202.h:16 */
#if defined(SHA3_512_RATE)
#undef SHA3_512_RATE
#endif

/* mlkem/fips202/fips202.h:20 */
#if defined(shake128ctx)
#undef shake128ctx
#endif

/* mlkem/fips202/fips202.h:31 */
#if defined(shake128_absorb_once)
#undef shake128_absorb_once
#endif

/* mlkem/fips202/fips202.h:58 */
#if defined(shake128_squeezeblocks)
#undef shake128_squeezeblocks
#endif

/* mlkem/fips202/fips202.h:80 */
#if defined(shake128_release)
#undef shake128_release
#endif

/* mlkem/fips202/fips202.h:85 */
#if defined(shake256)
#undef shake256
#endif

/* mlkem/fips202/fips202.h:106 */
#if defined(SHA3_256_HASHBYTES)
#undef SHA3_256_HASHBYTES
#endif

/* mlkem/fips202/fips202.h:107 */
#if defined(sha3_256)
#undef sha3_256
#endif

/* mlkem/fips202/fips202.h:126 */
#if defined(SHA3_512_HASHBYTES)
#undef SHA3_512_HASHBYTES
#endif

/* mlkem/fips202/fips202.h:127 */
#if defined(sha3_512)
#undef sha3_512
#endif

/* mlkem/fips202/fips202_backend.h:6 */
#if defined(MLKEM_NATIVE_FIPS202_IMPL_H)
#undef MLKEM_NATIVE_FIPS202_IMPL_H
#endif

/* mlkem/fips202/fips202x4.c:9 */
#if defined(shake256x4_ctx)
#undef shake256x4_ctx
#endif

/* mlkem/fips202/fips202x4.h:5 */
#if defined(FIPS_202X4_H)
#undef FIPS_202X4_H
#endif

/* mlkem/fips202/fips202x4.h:16 */
#if defined(shake128x4ctx)
#undef shake128x4ctx
#endif

/* mlkem/fips202/fips202x4.h:22 */
#if defined(shake128x4_absorb_once)
#undef shake128x4_absorb_once
#endif

/* mlkem/fips202/fips202x4.h:35 */
#if defined(shake128x4_squeezeblocks)
#undef shake128x4_squeezeblocks
#endif

/* mlkem/fips202/fips202x4.h:52 */
#if defined(shake128x4_release)
#undef shake128x4_release
#endif

/* mlkem/fips202/fips202x4.h:55 */
#if defined(shake256x4)
#undef shake256x4
#endif

/* mlkem/fips202/keccakf1600.c:21 */
#if defined(NROUNDS)
#undef NROUNDS
#endif

/* mlkem/fips202/keccakf1600.c:22 */
#if defined(ROL)
#undef ROL
#endif

/* mlkem/fips202/keccakf1600.h:5 */
#if defined(KECCAKF1600_H)
#undef KECCAKF1600_H
#endif

/* mlkem/fips202/keccakf1600.h:10 */
#if defined(KECCAK_LANES)
#undef KECCAK_LANES
#endif

/* mlkem/fips202/keccakf1600.h:19 */
#if defined(KeccakF1600_StateExtractBytes)
#undef KeccakF1600_StateExtractBytes
#endif

/* mlkem/fips202/keccakf1600.h:31 */
#if defined(KeccakF1600_StateXORBytes)
#undef KeccakF1600_StateXORBytes
#endif

/* mlkem/fips202/keccakf1600.h:42 */
#if defined(KeccakF1600x4_StateExtractBytes)
#undef KeccakF1600x4_StateExtractBytes
#endif

/* mlkem/fips202/keccakf1600.h:49 */
#if defined(KeccakF1600x4_StateXORBytes)
#undef KeccakF1600x4_StateXORBytes
#endif

/* mlkem/fips202/keccakf1600.h:57 */
#if defined(KeccakF1600x4_StatePermute)
#undef KeccakF1600x4_StatePermute
#endif

/* mlkem/fips202/keccakf1600.h:61 */
#if defined(KeccakF1600_StatePermute)
#undef KeccakF1600_StatePermute
#endif

/* mlkem/fips202/keccakf1600.h:69 */
#if defined(KeccakF1600_StatePermute)
#undef KeccakF1600_StatePermute
#endif

/* mlkem/fips202/native/aarch64/cortex_a55.h:10 */
#if defined(FIPS202_NATIVE_PROFILE_H)
#undef FIPS202_NATIVE_PROFILE_H
#endif

/* mlkem/fips202/native/aarch64/cortex_a55.h:14 */
#if defined(MLKEM_NATIVE_FIPS202_BACKEND_AARCH64_A55)
#undef MLKEM_NATIVE_FIPS202_BACKEND_AARCH64_A55
#endif

/* mlkem/fips202/native/aarch64/cortex_a55.h:16 */
#if defined(MLKEM_NATIVE_FIPS202_BACKEND_NAME)
#undef MLKEM_NATIVE_FIPS202_BACKEND_NAME
#endif

/* mlkem/fips202/native/aarch64/cortex_a55.h:21 */
#if defined(MLKEM_NATIVE_FIPS202_BACKEND_IMPL)
#undef MLKEM_NATIVE_FIPS202_BACKEND_IMPL
#endif

/* mlkem/fips202/native/aarch64/default.h:10 */
#if defined(FIPS202_NATIVE_PROFILE_H)
#undef FIPS202_NATIVE_PROFILE_H
#endif

/* mlkem/fips202/native/aarch64/default.h:14 */
#if defined(MLKEM_NATIVE_FIPS202_BACKEND_AARCH64_DEFAULT)
#undef MLKEM_NATIVE_FIPS202_BACKEND_AARCH64_DEFAULT
#endif

/* mlkem/fips202/native/aarch64/default.h:16 */
#if defined(MLKEM_NATIVE_FIPS202_BACKEND_NAME)
#undef MLKEM_NATIVE_FIPS202_BACKEND_NAME
#endif

/* mlkem/fips202/native/aarch64/default.h:21 */
#if defined(MLKEM_NATIVE_FIPS202_BACKEND_IMPL)
#undef MLKEM_NATIVE_FIPS202_BACKEND_IMPL
#endif

/* mlkem/fips202/native/aarch64/src/cortex_a55_impl.h:10 */
#if defined(FIPS202_NATIVE_PROFILE_IMPL_H)
#undef FIPS202_NATIVE_PROFILE_IMPL_H
#endif

/* mlkem/fips202/native/aarch64/src/cortex_a55_impl.h:18 */
#if defined(MLKEM_USE_FIPS202_X1_NATIVE)
#undef MLKEM_USE_FIPS202_X1_NATIVE
#endif

/* mlkem/fips202/native/aarch64/src/default_impl.h:10 */
#if defined(FIPS202_NATIVE_PROFILE_IMPL_H)
#undef FIPS202_NATIVE_PROFILE_IMPL_H
#endif

/* mlkem/fips202/native/aarch64/src/default_impl.h:32 */
#if defined(MLKEM_USE_FIPS202_X1_NATIVE)
#undef MLKEM_USE_FIPS202_X1_NATIVE
#endif

/* mlkem/fips202/native/aarch64/src/default_impl.h:38 */
#if defined(MLKEM_USE_FIPS202_X1_NATIVE)
#undef MLKEM_USE_FIPS202_X1_NATIVE
#endif

/* mlkem/fips202/native/aarch64/src/default_impl.h:65 */
#if defined(MLKEM_USE_FIPS202_X2_NATIVE)
#undef MLKEM_USE_FIPS202_X2_NATIVE
#endif

/* mlkem/fips202/native/aarch64/src/default_impl.h:71 */
#if defined(MLKEM_USE_FIPS202_X4_NATIVE)
#undef MLKEM_USE_FIPS202_X4_NATIVE
#endif

/* mlkem/fips202/native/aarch64/src/default_impl.h:81 */
#if defined(MLKEM_USE_FIPS202_X4_NATIVE)
#undef MLKEM_USE_FIPS202_X4_NATIVE
#endif

/* mlkem/fips202/native/aarch64/src/fips202_native_aarch64.h:5 */
#if defined(FIPS202_AARCH64_NATIVE_H)
#undef FIPS202_AARCH64_NATIVE_H
#endif

/* mlkem/fips202/native/aarch64/src/fips202_native_aarch64.h:10 */
#if defined(keccak_f1600_x1_scalar_asm_opt)
#undef keccak_f1600_x1_scalar_asm_opt
#endif

/* mlkem/fips202/native/aarch64/src/fips202_native_aarch64.h:14 */
#if defined(keccak_f1600_x1_v84a_asm_clean)
#undef keccak_f1600_x1_v84a_asm_clean
#endif

/* mlkem/fips202/native/aarch64/src/fips202_native_aarch64.h:18 */
#if defined(keccak_f1600_x2_v84a_asm_clean)
#undef keccak_f1600_x2_v84a_asm_clean
#endif

/* mlkem/fips202/native/aarch64/src/fips202_native_aarch64.h:22 */
#if defined(keccak_f1600_x2_v8a_v84a_asm_hybrid)
#undef keccak_f1600_x2_v8a_v84a_asm_hybrid
#endif

/* mlkem/fips202/native/aarch64/src/fips202_native_aarch64.h:26 */
#if defined(keccak_f1600_x4_scalar_v8a_asm_hybrid_opt)
#undef keccak_f1600_x4_scalar_v8a_asm_hybrid_opt
#endif

/* mlkem/fips202/native/aarch64/src/fips202_native_aarch64.h:31 */
#if defined(keccak_f1600_x4_scalar_v84a_asm_hybrid_opt)
#undef keccak_f1600_x4_scalar_v84a_asm_hybrid_opt
#endif

/* mlkem/fips202/native/aarch64/src/fips202_native_aarch64.h:36 */
#if defined(keccak_f1600_x4_scalar_v8a_v84a_hybrid_asm_opt)
#undef keccak_f1600_x4_scalar_v8a_v84a_hybrid_asm_opt
#endif

/* mlkem/fips202/native/aarch64/src/fips202_native_aarch64.h:41 */
#if defined(keccakf1600_round_constants)
#undef keccakf1600_round_constants
#endif

/* mlkem/fips202/native/aarch64/src/keccakf1600_round_constants.c:27 */
#if defined(empty_cu_keccakf1600_round_constants)
#undef empty_cu_keccakf1600_round_constants
#endif

/* mlkem/fips202/native/api.h:17 */
#if defined(MLKEM_NATIVE_FIPS202_NATIVE_API_H)
#undef MLKEM_NATIVE_FIPS202_NATIVE_API_H
#endif

/* mlkem/fips202/native/default.h:6 */
#if defined(MLKEM_NATIVE_FIPS202_BACKEND_DEFAULT_H)
#undef MLKEM_NATIVE_FIPS202_BACKEND_DEFAULT_H
#endif

/* mlkem/fips202/native/x86_64/src/KeccakP-1600-times4-SIMD256.c:49 */
#if defined(ANDnu256)
#undef ANDnu256
#endif

/* mlkem/fips202/native/x86_64/src/KeccakP-1600-times4-SIMD256.c:50 */
#if defined(CONST256)
#undef CONST256
#endif

/* mlkem/fips202/native/x86_64/src/KeccakP-1600-times4-SIMD256.c:51 */
#if defined(CONST256_64)
#undef CONST256_64
#endif

/* mlkem/fips202/native/x86_64/src/KeccakP-1600-times4-SIMD256.c:52 */
#if defined(ROL64in256)
#undef ROL64in256
#endif

/* mlkem/fips202/native/x86_64/src/KeccakP-1600-times4-SIMD256.c:54 */
#if defined(ROL64in256_8)
#undef ROL64in256_8
#endif

/* mlkem/fips202/native/x86_64/src/KeccakP-1600-times4-SIMD256.c:55 */
#if defined(ROL64in256_56)
#undef ROL64in256_56
#endif

/* mlkem/fips202/native/x86_64/src/KeccakP-1600-times4-SIMD256.c:60 */
#if defined(STORE256)
#undef STORE256
#endif

/* mlkem/fips202/native/x86_64/src/KeccakP-1600-times4-SIMD256.c:61 */
#if defined(XOR256)
#undef XOR256
#endif

/* mlkem/fips202/native/x86_64/src/KeccakP-1600-times4-SIMD256.c:62 */
#if defined(XOReq256)
#undef XOReq256
#endif

/* mlkem/fips202/native/x86_64/src/KeccakP-1600-times4-SIMD256.c:65 */
#if defined(SnP_laneLengthInBytes)
#undef SnP_laneLengthInBytes
#endif

/* mlkem/fips202/native/x86_64/src/KeccakP-1600-times4-SIMD256.c:67 */
#if defined(declareABCDE)
#undef declareABCDE
#endif

/* mlkem/fips202/native/x86_64/src/KeccakP-1600-times4-SIMD256.c:87 */
#if defined(prepareTheta)
#undef prepareTheta
#endif

/* mlkem/fips202/native/x86_64/src/KeccakP-1600-times4-SIMD256.c:98 */
#if defined(thetaRhoPiChiIotaPrepareTheta)
#undef thetaRhoPiChiIotaPrepareTheta
#endif

/* mlkem/fips202/native/x86_64/src/KeccakP-1600-times4-SIMD256.c:221 */
#if defined(thetaRhoPiChiIota)
#undef thetaRhoPiChiIota
#endif

/* mlkem/fips202/native/x86_64/src/KeccakP-1600-times4-SIMD256.c:328 */
#if defined(copyFromState)
#undef copyFromState
#endif

/* mlkem/fips202/native/x86_64/src/KeccakP-1600-times4-SIMD256.c:362 */
#if defined(SCATTER_STORE256)
#undef SCATTER_STORE256
#endif

/* mlkem/fips202/native/x86_64/src/KeccakP-1600-times4-SIMD256.c:374 */
#if defined(copyToState)
#undef copyToState
#endif

/* mlkem/fips202/native/x86_64/src/KeccakP-1600-times4-SIMD256.c:401 */
#if defined(copyStateVariables)
#undef copyStateVariables
#endif

/* mlkem/fips202/native/x86_64/src/KeccakP-1600-times4-SIMD256.c:429 */
#if defined(FullUnrolling)
#undef FullUnrolling
#endif

/* mlkem/fips202/native/x86_64/src/KeccakP-1600-times4-SIMD256.c:431 */
#if defined(Unrolling)
#undef Unrolling
#endif

/* mlkem/fips202/native/x86_64/src/KeccakP-1600-times4-SIMD256.c:449 */
#if defined(empty_cu_avx2_keccakx4)
#undef empty_cu_avx2_keccakx4
#endif

/* mlkem/fips202/native/x86_64/src/KeccakP-1600-times4-SnP.h:21 */
#if defined(_KeccakP_1600_times4_SnP_h_)
#undef _KeccakP_1600_times4_SnP_h_
#endif

/* mlkem/fips202/native/x86_64/src/KeccakP-1600-times4-SnP.h:30 */
#if defined(KeccakP1600times4_statesAlignment)
#undef KeccakP1600times4_statesAlignment
#endif

/* mlkem/fips202/native/x86_64/src/KeccakP-1600-times4-SnP.h:32 */
#if defined(KeccakP1600times4_PermuteAll_24rounds)
#undef KeccakP1600times4_PermuteAll_24rounds
#endif

/* mlkem/fips202/native/x86_64/src/KeccakP-SIMD256-config.h:5 */
#if defined(KeccakP1600times4_implementation_config)
#undef KeccakP1600times4_implementation_config
#endif

/* mlkem/fips202/native/x86_64/src/KeccakP-SIMD256-config.h:6 */
#if defined(KeccakP1600times4_fullUnrolling)
#undef KeccakP1600times4_fullUnrolling
#endif

/* mlkem/fips202/native/x86_64/src/KeccakP-SIMD256-config.h:7 */
#if defined(KeccakP1600times4_useAVX2)
#undef KeccakP1600times4_useAVX2
#endif

/* mlkem/fips202/native/x86_64/src/KeccakP-align.h:21 */
#if defined(_keccakp_align_h_)
#undef _keccakp_align_h_
#endif

/* mlkem/fips202/native/x86_64/src/KeccakP-align.h:30 */
#if defined(ALIGN)
#undef ALIGN
#endif

/* mlkem/fips202/native/x86_64/src/KeccakP-align.h:32 */
#if defined(ALIGN)
#undef ALIGN
#endif

/* mlkem/fips202/native/x86_64/src/KeccakP-align.h:34 */
#if defined(ALIGN)
#undef ALIGN
#endif

/* mlkem/fips202/native/x86_64/src/KeccakP-align.h:36 */
#if defined(ALIGN)
#undef ALIGN
#endif

/* mlkem/fips202/native/x86_64/src/KeccakP-brg_endian.h:34 */
#if defined(_KECCAKP_BRG_ENDIAN_H)
#undef _KECCAKP_BRG_ENDIAN_H
#endif

/* mlkem/fips202/native/x86_64/src/KeccakP-brg_endian.h:36 */
#if defined(IS_BIG_ENDIAN)
#undef IS_BIG_ENDIAN
#endif

/* mlkem/fips202/native/x86_64/src/KeccakP-brg_endian.h:37 */
#if defined(IS_LITTLE_ENDIAN)
#undef IS_LITTLE_ENDIAN
#endif

/* mlkem/fips202/native/x86_64/src/KeccakP-brg_endian.h:65 */
#if defined(PLATFORM_BYTE_ORDER)
#undef PLATFORM_BYTE_ORDER
#endif

/* mlkem/fips202/native/x86_64/src/KeccakP-brg_endian.h:67 */
#if defined(PLATFORM_BYTE_ORDER)
#undef PLATFORM_BYTE_ORDER
#endif

/* mlkem/fips202/native/x86_64/src/KeccakP-brg_endian.h:70 */
#if defined(PLATFORM_BYTE_ORDER)
#undef PLATFORM_BYTE_ORDER
#endif

/* mlkem/fips202/native/x86_64/src/KeccakP-brg_endian.h:72 */
#if defined(PLATFORM_BYTE_ORDER)
#undef PLATFORM_BYTE_ORDER
#endif

/* mlkem/fips202/native/x86_64/src/KeccakP-brg_endian.h:77 */
#if defined(PLATFORM_BYTE_ORDER)
#undef PLATFORM_BYTE_ORDER
#endif

/* mlkem/fips202/native/x86_64/src/KeccakP-brg_endian.h:79 */
#if defined(PLATFORM_BYTE_ORDER)
#undef PLATFORM_BYTE_ORDER
#endif

/* mlkem/fips202/native/x86_64/src/KeccakP-brg_endian.h:82 */
#if defined(PLATFORM_BYTE_ORDER)
#undef PLATFORM_BYTE_ORDER
#endif

/* mlkem/fips202/native/x86_64/src/KeccakP-brg_endian.h:84 */
#if defined(PLATFORM_BYTE_ORDER)
#undef PLATFORM_BYTE_ORDER
#endif

/* mlkem/fips202/native/x86_64/src/KeccakP-brg_endian.h:89 */
#if defined(PLATFORM_BYTE_ORDER)
#undef PLATFORM_BYTE_ORDER
#endif

/* mlkem/fips202/native/x86_64/src/KeccakP-brg_endian.h:91 */
#if defined(PLATFORM_BYTE_ORDER)
#undef PLATFORM_BYTE_ORDER
#endif

/* mlkem/fips202/native/x86_64/src/KeccakP-brg_endian.h:94 */
#if defined(PLATFORM_BYTE_ORDER)
#undef PLATFORM_BYTE_ORDER
#endif

/* mlkem/fips202/native/x86_64/src/KeccakP-brg_endian.h:96 */
#if defined(PLATFORM_BYTE_ORDER)
#undef PLATFORM_BYTE_ORDER
#endif

/* mlkem/fips202/native/x86_64/src/KeccakP-brg_endian.h:101 */
#if defined(PLATFORM_BYTE_ORDER)
#undef PLATFORM_BYTE_ORDER
#endif

/* mlkem/fips202/native/x86_64/src/KeccakP-brg_endian.h:103 */
#if defined(PLATFORM_BYTE_ORDER)
#undef PLATFORM_BYTE_ORDER
#endif

/* mlkem/fips202/native/x86_64/src/KeccakP-brg_endian.h:106 */
#if defined(PLATFORM_BYTE_ORDER)
#undef PLATFORM_BYTE_ORDER
#endif

/* mlkem/fips202/native/x86_64/src/KeccakP-brg_endian.h:108 */
#if defined(PLATFORM_BYTE_ORDER)
#undef PLATFORM_BYTE_ORDER
#endif

/* mlkem/fips202/native/x86_64/src/KeccakP-brg_endian.h:122 */
#if defined(PLATFORM_BYTE_ORDER)
#undef PLATFORM_BYTE_ORDER
#endif

/* mlkem/fips202/native/x86_64/src/KeccakP-brg_endian.h:131 */
#if defined(PLATFORM_BYTE_ORDER)
#undef PLATFORM_BYTE_ORDER
#endif

/* mlkem/fips202/native/x86_64/src/KeccakP-brg_endian.h:135 */
#if defined(PLATFORM_BYTE_ORDER)
#undef PLATFORM_BYTE_ORDER
#endif

/* mlkem/fips202/native/x86_64/src/KeccakP-brg_endian.h:137 */
#if defined(PLATFORM_BYTE_ORDER)
#undef PLATFORM_BYTE_ORDER
#endif

/* mlkem/fips202/native/x86_64/src/KeccakP-brg_endian.h:140 */
#if defined(PLATFORM_BYTE_ORDER)
#undef PLATFORM_BYTE_ORDER
#endif

/* mlkem/fips202/native/x86_64/src/KeccakP-brg_endian.h:142 */
#if defined(PLATFORM_BYTE_ORDER)
#undef PLATFORM_BYTE_ORDER
#endif

/* mlkem/fips202/native/x86_64/src/xkcp_impl.h:10 */
#if defined(MLKEM_NATIVE_FIPS202_PROFILE_IMPL_H)
#undef MLKEM_NATIVE_FIPS202_PROFILE_IMPL_H
#endif

/* mlkem/fips202/native/x86_64/src/xkcp_impl.h:14 */
#if defined(MLKEM_USE_FIPS202_X4_NATIVE)
#undef MLKEM_USE_FIPS202_X4_NATIVE
#endif

/* mlkem/fips202/native/x86_64/xkcp.h:10 */
#if defined(MLKEM_NATIVE_FIPS202_PROFILE_H)
#undef MLKEM_NATIVE_FIPS202_PROFILE_H
#endif

/* mlkem/fips202/native/x86_64/xkcp.h:14 */
#if defined(MLKEM_NATIVE_FIPS202_BACKEND_X86_64_XKCP)
#undef MLKEM_NATIVE_FIPS202_BACKEND_X86_64_XKCP
#endif

/* mlkem/fips202/native/x86_64/xkcp.h:16 */
#if defined(MLKEM_NATIVE_FIPS202_BACKEND_NAME)
#undef MLKEM_NATIVE_FIPS202_BACKEND_NAME
#endif

/* mlkem/fips202/native/x86_64/xkcp.h:21 */
#if defined(MLKEM_NATIVE_FIPS202_BACKEND_IMPL)
#undef MLKEM_NATIVE_FIPS202_BACKEND_IMPL
#endif

/* mlkem/indcpa.c:133 */
#if defined(MLKEM_GEN_MATRIX_NBLOCKS)
#undef MLKEM_GEN_MATRIX_NBLOCKS
#endif

/* mlkem/indcpa.h:5 */
#if defined(INDCPA_H)
#undef INDCPA_H
#endif

/* mlkem/indcpa.h:12 */
#if defined(gen_matrix)
#undef gen_matrix
#endif

/* mlkem/indcpa.h:35 */
#if defined(indcpa_keypair_derand)
#undef indcpa_keypair_derand
#endif

/* mlkem/indcpa.h:60 */
#if defined(indcpa_enc)
#undef indcpa_enc
#endif

/* mlkem/indcpa.h:88 */
#if defined(indcpa_dec)
#undef indcpa_dec
#endif

/* mlkem/kem.h:5 */
#if defined(KEM_H)
#undef KEM_H
#endif

/* mlkem/kem.h:11 */
#if defined(CRYPTO_SECRETKEYBYTES)
#undef CRYPTO_SECRETKEYBYTES
#endif

/* mlkem/kem.h:12 */
#if defined(CRYPTO_PUBLICKEYBYTES)
#undef CRYPTO_PUBLICKEYBYTES
#endif

/* mlkem/kem.h:13 */
#if defined(CRYPTO_CIPHERTEXTBYTES)
#undef CRYPTO_CIPHERTEXTBYTES
#endif

/* mlkem/kem.h:14 */
#if defined(CRYPTO_BYTES)
#undef CRYPTO_BYTES
#endif

/* mlkem/kem.h:17 */
#if defined(CRYPTO_ALGNAME)
#undef CRYPTO_ALGNAME
#endif

/* mlkem/kem.h:19 */
#if defined(CRYPTO_ALGNAME)
#undef CRYPTO_ALGNAME
#endif

/* mlkem/kem.h:21 */
#if defined(CRYPTO_ALGNAME)
#undef CRYPTO_ALGNAME
#endif

/* mlkem/kem.h:24 */
#if defined(crypto_kem_keypair_derand)
#undef crypto_kem_keypair_derand
#endif

/* mlkem/kem.h:50 */
#if defined(crypto_kem_keypair)
#undef crypto_kem_keypair
#endif

/* mlkem/kem.h:72 */
#if defined(crypto_kem_enc_derand)
#undef crypto_kem_enc_derand
#endif

/* mlkem/kem.h:103 */
#if defined(crypto_kem_enc)
#undef crypto_kem_enc
#endif

/* mlkem/kem.h:129 */
#if defined(crypto_kem_dec)
#undef crypto_kem_dec
#endif

/* mlkem/namespace.h:5 */
#if defined(MLKEM_NATIVE_NAMESPACE_H)
#undef MLKEM_NATIVE_NAMESPACE_H
#endif

/* mlkem/namespace.h:8 */
#if defined(MLKEM_NATIVE_ARITH_BACKEND_NAME)
#undef MLKEM_NATIVE_ARITH_BACKEND_NAME
#endif

/* mlkem/namespace.h:13 */
#if defined(MLKEM_PARAM_NAME)
#undef MLKEM_PARAM_NAME
#endif

/* mlkem/namespace.h:15 */
#if defined(MLKEM_PARAM_NAME)
#undef MLKEM_PARAM_NAME
#endif

/* mlkem/namespace.h:17 */
#if defined(MLKEM_PARAM_NAME)
#undef MLKEM_PARAM_NAME
#endif

/* mlkem/namespace.h:22 */
#if defined(___MLKEM_DEFAULT_NAMESPACE)
#undef ___MLKEM_DEFAULT_NAMESPACE
#endif

/* mlkem/namespace.h:23 */
#if defined(__MLKEM_DEFAULT_NAMESPACE)
#undef __MLKEM_DEFAULT_NAMESPACE
#endif

/* mlkem/namespace.h:30 */
#if defined(MLKEM_DEFAULT_NAMESPACE)
#undef MLKEM_DEFAULT_NAMESPACE
#endif

/* mlkem/namespace.h:35 */
#if defined(MLKEM_NATIVE_FIPS202_BACKEND_NAME)
#undef MLKEM_NATIVE_FIPS202_BACKEND_NAME
#endif

/* mlkem/namespace.h:38 */
#if defined(___FIPS202_DEFAULT_NAMESPACE)
#undef ___FIPS202_DEFAULT_NAMESPACE
#endif

/* mlkem/namespace.h:39 */
#if defined(__FIPS202_DEFAULT_NAMESPACE)
#undef __FIPS202_DEFAULT_NAMESPACE
#endif

/* mlkem/namespace.h:46 */
#if defined(FIPS202_DEFAULT_NAMESPACE)
#undef FIPS202_DEFAULT_NAMESPACE
#endif

/* mlkem/native/aarch64/clean.h:10 */
#if defined(MLKEM_NATIVE_ARITH_PROFILE_H)
#undef MLKEM_NATIVE_ARITH_PROFILE_H
#endif

/* mlkem/native/aarch64/clean.h:14 */
#if defined(MLKEM_NATIVE_ARITH_BACKEND_AARCH64_CLEAN)
#undef MLKEM_NATIVE_ARITH_BACKEND_AARCH64_CLEAN
#endif

/* mlkem/native/aarch64/clean.h:16 */
#if defined(MLKEM_NATIVE_ARITH_BACKEND_NAME)
#undef MLKEM_NATIVE_ARITH_BACKEND_NAME
#endif

/* mlkem/native/aarch64/clean.h:21 */
#if defined(MLKEM_NATIVE_ARITH_BACKEND_IMPL)
#undef MLKEM_NATIVE_ARITH_BACKEND_IMPL
#endif

/* mlkem/native/aarch64/opt.h:10 */
#if defined(MLKEM_NATIVE_ARITH_PROFILE_H)
#undef MLKEM_NATIVE_ARITH_PROFILE_H
#endif

/* mlkem/native/aarch64/opt.h:14 */
#if defined(MLKEM_NATIVE_ARITH_BACKEND_AARCH64_OPT)
#undef MLKEM_NATIVE_ARITH_BACKEND_AARCH64_OPT
#endif

/* mlkem/native/aarch64/opt.h:16 */
#if defined(MLKEM_NATIVE_ARITH_BACKEND_NAME)
#undef MLKEM_NATIVE_ARITH_BACKEND_NAME
#endif

/* mlkem/native/aarch64/opt.h:21 */
#if defined(MLKEM_NATIVE_ARITH_BACKEND_IMPL)
#undef MLKEM_NATIVE_ARITH_BACKEND_IMPL
#endif

/* mlkem/native/aarch64/src/aarch64_zetas.c:172 */
#if defined(empty_cu_aarch64_zetas)
#undef empty_cu_aarch64_zetas
#endif

/* mlkem/native/aarch64/src/arith_native_aarch64.h:5 */
#if defined(MLKEM_AARCH64_NATIVE_H)
#undef MLKEM_AARCH64_NATIVE_H
#endif

/* mlkem/native/aarch64/src/arith_native_aarch64.h:10 */
#if defined(aarch64_ntt_zetas_layer01234)
#undef aarch64_ntt_zetas_layer01234
#endif

/* mlkem/native/aarch64/src/arith_native_aarch64.h:12 */
#if defined(aarch64_ntt_zetas_layer56)
#undef aarch64_ntt_zetas_layer56
#endif

/* mlkem/native/aarch64/src/arith_native_aarch64.h:13 */
#if defined(aarch64_invntt_zetas_layer01234)
#undef aarch64_invntt_zetas_layer01234
#endif

/* mlkem/native/aarch64/src/arith_native_aarch64.h:15 */
#if defined(aarch64_invntt_zetas_layer56)
#undef aarch64_invntt_zetas_layer56
#endif

/* mlkem/native/aarch64/src/arith_native_aarch64.h:17 */
#if defined(aarch64_zetas_mulcache_native)
#undef aarch64_zetas_mulcache_native
#endif

/* mlkem/native/aarch64/src/arith_native_aarch64.h:19 */
#if defined(aarch64_zetas_mulcache_twisted_native)
#undef aarch64_zetas_mulcache_twisted_native
#endif

/* mlkem/native/aarch64/src/arith_native_aarch64.h:21 */
#if defined(rej_uniform_table)
#undef rej_uniform_table
#endif

/* mlkem/native/aarch64/src/arith_native_aarch64.h:31 */
#if defined(ntt_asm_clean)
#undef ntt_asm_clean
#endif

/* mlkem/native/aarch64/src/arith_native_aarch64.h:34 */
#if defined(ntt_asm_opt)
#undef ntt_asm_opt
#endif

/* mlkem/native/aarch64/src/arith_native_aarch64.h:37 */
#if defined(intt_asm_clean)
#undef intt_asm_clean
#endif

/* mlkem/native/aarch64/src/arith_native_aarch64.h:40 */
#if defined(intt_asm_opt)
#undef intt_asm_opt
#endif

/* mlkem/native/aarch64/src/arith_native_aarch64.h:43 */
#if defined(rej_uniform_asm_clean)
#undef rej_uniform_asm_clean
#endif

/* mlkem/native/aarch64/src/arith_native_aarch64.h:47 */
#if defined(poly_reduce_asm_clean)
#undef poly_reduce_asm_clean
#endif

/* mlkem/native/aarch64/src/arith_native_aarch64.h:50 */
#if defined(poly_reduce_asm_opt)
#undef poly_reduce_asm_opt
#endif

/* mlkem/native/aarch64/src/arith_native_aarch64.h:53 */
#if defined(poly_tomont_asm_clean)
#undef poly_tomont_asm_clean
#endif

/* mlkem/native/aarch64/src/arith_native_aarch64.h:56 */
#if defined(poly_tomont_asm_opt)
#undef poly_tomont_asm_opt
#endif

/* mlkem/native/aarch64/src/arith_native_aarch64.h:59 */
#if defined(poly_mulcache_compute_asm_clean)
#undef poly_mulcache_compute_asm_clean
#endif

/* mlkem/native/aarch64/src/arith_native_aarch64.h:65 */
#if defined(poly_mulcache_compute_asm_opt)
#undef poly_mulcache_compute_asm_opt
#endif

/* mlkem/native/aarch64/src/arith_native_aarch64.h:70 */
#if defined(poly_tobytes_asm_clean)
#undef poly_tobytes_asm_clean
#endif

/* mlkem/native/aarch64/src/arith_native_aarch64.h:73 */
#if defined(poly_tobytes_asm_opt)
#undef poly_tobytes_asm_opt
#endif

/* mlkem/native/aarch64/src/arith_native_aarch64.h:76 */
#if defined(polyvec_basemul_acc_montgomery_cached_asm_clean)
#undef polyvec_basemul_acc_montgomery_cached_asm_clean
#endif

/* mlkem/native/aarch64/src/arith_native_aarch64.h:83 */
#if defined(polyvec_basemul_acc_montgomery_cached_asm_opt)
#undef polyvec_basemul_acc_montgomery_cached_asm_opt
#endif

/* mlkem/native/aarch64/src/clean_impl.h:10 */
#if defined(MLKEM_NATIVE_ARITH_PROFILE_IMPL_H)
#undef MLKEM_NATIVE_ARITH_PROFILE_IMPL_H
#endif

/* mlkem/native/aarch64/src/clean_impl.h:18 */
#if defined(MLKEM_USE_NATIVE_NTT)
#undef MLKEM_USE_NATIVE_NTT
#endif

/* mlkem/native/aarch64/src/clean_impl.h:19 */
#if defined(MLKEM_USE_NATIVE_INTT)
#undef MLKEM_USE_NATIVE_INTT
#endif

/* mlkem/native/aarch64/src/clean_impl.h:20 */
#if defined(MLKEM_USE_NATIVE_POLY_REDUCE)
#undef MLKEM_USE_NATIVE_POLY_REDUCE
#endif

/* mlkem/native/aarch64/src/clean_impl.h:21 */
#if defined(MLKEM_USE_NATIVE_POLY_TOMONT)
#undef MLKEM_USE_NATIVE_POLY_TOMONT
#endif

/* mlkem/native/aarch64/src/clean_impl.h:22 */
#if defined(MLKEM_USE_NATIVE_POLY_MULCACHE_COMPUTE)
#undef MLKEM_USE_NATIVE_POLY_MULCACHE_COMPUTE
#endif

/* mlkem/native/aarch64/src/clean_impl.h:23 */
#if defined(MLKEM_USE_NATIVE_POLYVEC_BASEMUL_ACC_MONTGOMERY_CACHED)
#undef MLKEM_USE_NATIVE_POLYVEC_BASEMUL_ACC_MONTGOMERY_CACHED
#endif

/* mlkem/native/aarch64/src/clean_impl.h:24 */
#if defined(MLKEM_USE_NATIVE_POLY_TOBYTES)
#undef MLKEM_USE_NATIVE_POLY_TOBYTES
#endif

/* mlkem/native/aarch64/src/clean_impl.h:25 */
#if defined(MLKEM_USE_NATIVE_REJ_UNIFORM)
#undef MLKEM_USE_NATIVE_REJ_UNIFORM
#endif

/* mlkem/native/aarch64/src/clean_impl.h:33 */
#if defined(INVNTT_BOUND_NATIVE)
#undef INVNTT_BOUND_NATIVE
#endif

/* mlkem/native/aarch64/src/consts.h:6 */
#if defined(MLKEM_NATIVE_AARCH64_CONSTS)
#undef MLKEM_NATIVE_AARCH64_CONSTS
#endif

/* mlkem/native/aarch64/src/consts.h:11 */
#if defined(zetas_mulcache_native)
#undef zetas_mulcache_native
#endif

/* mlkem/native/aarch64/src/consts.h:14 */
#if defined(zetas_mulcache_twisted_native)
#undef zetas_mulcache_twisted_native
#endif

/* mlkem/native/aarch64/src/opt_impl.h:10 */
#if defined(MLKEM_NATIVE_ARITH_PROFILE_IMPL_H)
#undef MLKEM_NATIVE_ARITH_PROFILE_IMPL_H
#endif

/* mlkem/native/aarch64/src/opt_impl.h:18 */
#if defined(MLKEM_USE_NATIVE_NTT)
#undef MLKEM_USE_NATIVE_NTT
#endif

/* mlkem/native/aarch64/src/opt_impl.h:19 */
#if defined(MLKEM_USE_NATIVE_INTT)
#undef MLKEM_USE_NATIVE_INTT
#endif

/* mlkem/native/aarch64/src/opt_impl.h:20 */
#if defined(MLKEM_USE_NATIVE_POLY_REDUCE)
#undef MLKEM_USE_NATIVE_POLY_REDUCE
#endif

/* mlkem/native/aarch64/src/opt_impl.h:21 */
#if defined(MLKEM_USE_NATIVE_POLY_TOMONT)
#undef MLKEM_USE_NATIVE_POLY_TOMONT
#endif

/* mlkem/native/aarch64/src/opt_impl.h:22 */
#if defined(MLKEM_USE_NATIVE_POLY_MULCACHE_COMPUTE)
#undef MLKEM_USE_NATIVE_POLY_MULCACHE_COMPUTE
#endif

/* mlkem/native/aarch64/src/opt_impl.h:23 */
#if defined(MLKEM_USE_NATIVE_POLYVEC_BASEMUL_ACC_MONTGOMERY_CACHED)
#undef MLKEM_USE_NATIVE_POLYVEC_BASEMUL_ACC_MONTGOMERY_CACHED
#endif

/* mlkem/native/aarch64/src/opt_impl.h:24 */
#if defined(MLKEM_USE_NATIVE_POLY_TOBYTES)
#undef MLKEM_USE_NATIVE_POLY_TOBYTES
#endif

/* mlkem/native/aarch64/src/opt_impl.h:25 */
#if defined(MLKEM_USE_NATIVE_REJ_UNIFORM)
#undef MLKEM_USE_NATIVE_REJ_UNIFORM
#endif

/* mlkem/native/aarch64/src/opt_impl.h:27 */
#if defined(NTT_BOUND_NATIVE)
#undef NTT_BOUND_NATIVE
#endif

/* mlkem/native/aarch64/src/opt_impl.h:34 */
#if defined(INVNTT_BOUND_NATIVE)
#undef INVNTT_BOUND_NATIVE
#endif

/* mlkem/native/aarch64/src/rej_uniform_table.c:284 */
#if defined(empty_cu_aarch64_rej_uniform_table)
#undef empty_cu_aarch64_rej_uniform_table
#endif

/* mlkem/native/api.h:22 */
#if defined(MLKEM_NATIVE_ARITH_NATIVE_API_H)
#undef MLKEM_NATIVE_ARITH_NATIVE_API_H
#endif

/* mlkem/native/default.h:5 */
#if defined(MLKEM_NATIVE_ARITH_BACKEND_DEFAULT_H)
#undef MLKEM_NATIVE_ARITH_BACKEND_DEFAULT_H
#endif

/* mlkem/native/x86_64/default.h:10 */
#if defined(MLKEM_NATIVE_ARITH_PROFILE_H)
#undef MLKEM_NATIVE_ARITH_PROFILE_H
#endif

/* mlkem/native/x86_64/default.h:14 */
#if defined(MLKEM_NATIVE_ARITH_BACKEND_X86_64_DEFAULT)
#undef MLKEM_NATIVE_ARITH_BACKEND_X86_64_DEFAULT
#endif

/* mlkem/native/x86_64/default.h:16 */
#if defined(MLKEM_NATIVE_ARITH_BACKEND_NAME)
#undef MLKEM_NATIVE_ARITH_BACKEND_NAME
#endif

/* mlkem/native/x86_64/default.h:21 */
#if defined(MLKEM_NATIVE_ARITH_BACKEND_IMPL)
#undef MLKEM_NATIVE_ARITH_BACKEND_IMPL
#endif

/* mlkem/native/x86_64/src/align.h:11 */
#if defined(ALIGN_H)
#undef ALIGN_H
#endif

/* mlkem/native/x86_64/src/align.h:16 */
#if defined(ALIGNED_UINT8)
#undef ALIGNED_UINT8
#endif

/* mlkem/native/x86_64/src/align.h:23 */
#if defined(ALIGNED_INT16)
#undef ALIGNED_INT16
#endif

/* mlkem/native/x86_64/src/arith_native_x86_64.h:5 */
#if defined(MLKEM_X86_64_NATIVE_H)
#undef MLKEM_X86_64_NATIVE_H
#endif

/* mlkem/native/x86_64/src/arith_native_x86_64.h:15 */
#if defined(REJ_UNIFORM_AVX_NBLOCKS)
#undef REJ_UNIFORM_AVX_NBLOCKS
#endif

/* mlkem/native/x86_64/src/arith_native_x86_64.h:17 */
#if defined(REJ_UNIFORM_AVX_BUFLEN)
#undef REJ_UNIFORM_AVX_BUFLEN
#endif

/* mlkem/native/x86_64/src/arith_native_x86_64.h:19 */
#if defined(rej_uniform_avx2)
#undef rej_uniform_avx2
#endif

/* mlkem/native/x86_64/src/arith_native_x86_64.h:22 */
#if defined(rej_uniform_table)
#undef rej_uniform_table
#endif

/* mlkem/native/x86_64/src/arith_native_x86_64.h:25 */
#if defined(ntt_avx2)
#undef ntt_avx2
#endif

/* mlkem/native/x86_64/src/arith_native_x86_64.h:28 */
#if defined(invntt_avx2)
#undef invntt_avx2
#endif

/* mlkem/native/x86_64/src/arith_native_x86_64.h:31 */
#if defined(nttpack_avx2)
#undef nttpack_avx2
#endif

/* mlkem/native/x86_64/src/arith_native_x86_64.h:34 */
#if defined(nttunpack_avx2)
#undef nttunpack_avx2
#endif

/* mlkem/native/x86_64/src/arith_native_x86_64.h:37 */
#if defined(reduce_avx2)
#undef reduce_avx2
#endif

/* mlkem/native/x86_64/src/arith_native_x86_64.h:40 */
#if defined(basemul_avx2)
#undef basemul_avx2
#endif

/* mlkem/native/x86_64/src/arith_native_x86_64.h:44 */
#if defined(polyvec_basemul_acc_montgomery_cached_avx2)
#undef polyvec_basemul_acc_montgomery_cached_avx2
#endif

/* mlkem/native/x86_64/src/arith_native_x86_64.h:50 */
#if defined(ntttobytes_avx2)
#undef ntttobytes_avx2
#endif

/* mlkem/native/x86_64/src/arith_native_x86_64.h:53 */
#if defined(nttfrombytes_avx2)
#undef nttfrombytes_avx2
#endif

/* mlkem/native/x86_64/src/arith_native_x86_64.h:56 */
#if defined(tomont_avx2)
#undef tomont_avx2
#endif

/* mlkem/native/x86_64/src/basemul.c:64 */
#if defined(empty_cu_avx2_basemul)
#undef empty_cu_avx2_basemul
#endif

/* mlkem/native/x86_64/src/consts.c:17 */
#if defined(Q)
#undef Q
#endif

/* mlkem/native/x86_64/src/consts.c:18 */
#if defined(MONT)
#undef MONT
#endif

/* mlkem/native/x86_64/src/consts.c:19 */
#if defined(QINV)
#undef QINV
#endif

/* mlkem/native/x86_64/src/consts.c:20 */
#if defined(V)
#undef V
#endif

/* mlkem/native/x86_64/src/consts.c:21 */
#if defined(FHI)
#undef FHI
#endif

/* mlkem/native/x86_64/src/consts.c:22 */
#if defined(FLO)
#undef FLO
#endif

/* mlkem/native/x86_64/src/consts.c:23 */
#if defined(MONTSQHI)
#undef MONTSQHI
#endif

/* mlkem/native/x86_64/src/consts.c:24 */
#if defined(MONTSQLO)
#undef MONTSQLO
#endif

/* mlkem/native/x86_64/src/consts.c:25 */
#if defined(MASK)
#undef MASK
#endif

/* mlkem/native/x86_64/src/consts.c:26 */
#if defined(SHIFT)
#undef SHIFT
#endif

/* mlkem/native/x86_64/src/consts.c:29 */
#if defined(_16XQ)
#undef _16XQ
#endif

/* mlkem/native/x86_64/src/consts.c:34 */
#if defined(_16XQINV)
#undef _16XQINV
#endif

/* mlkem/native/x86_64/src/consts.c:39 */
#if defined(_16XV)
#undef _16XV
#endif

/* mlkem/native/x86_64/src/consts.c:44 */
#if defined(_16XFLO)
#undef _16XFLO
#endif

/* mlkem/native/x86_64/src/consts.c:49 */
#if defined(_16XFHI)
#undef _16XFHI
#endif

/* mlkem/native/x86_64/src/consts.c:54 */
#if defined(_16XMONTSQLO)
#undef _16XMONTSQLO
#endif

/* mlkem/native/x86_64/src/consts.c:59 */
#if defined(_16XMONTSQHI)
#undef _16XMONTSQHI
#endif

/* mlkem/native/x86_64/src/consts.c:64 */
#if defined(_16XMASK)
#undef _16XMASK
#endif

/* mlkem/native/x86_64/src/consts.c:69 */
#if defined(_REVIDXB)
#undef _REVIDXB
#endif

/* mlkem/native/x86_64/src/consts.c:74 */
#if defined(_REVIDXD)
#undef _REVIDXD
#endif

/* mlkem/native/x86_64/src/consts.c:79 */
#if defined(_ZETAS_EXP)
#undef _ZETAS_EXP
#endif

/* mlkem/native/x86_64/src/consts.c:82 */
#if defined(_16XSHIFT)
#undef _16XSHIFT
#endif

/* mlkem/native/x86_64/src/consts.c:90 */
#if defined(empty_cu_consts)
#undef empty_cu_consts
#endif

/* mlkem/native/x86_64/src/consts.h:11 */
#if defined(CONSTS_H)
#undef CONSTS_H
#endif

/* mlkem/native/x86_64/src/consts.h:15 */
#if defined(_16XQ)
#undef _16XQ
#endif

/* mlkem/native/x86_64/src/consts.h:16 */
#if defined(_16XQINV)
#undef _16XQINV
#endif

/* mlkem/native/x86_64/src/consts.h:17 */
#if defined(_16XV)
#undef _16XV
#endif

/* mlkem/native/x86_64/src/consts.h:18 */
#if defined(_16XFLO)
#undef _16XFLO
#endif

/* mlkem/native/x86_64/src/consts.h:19 */
#if defined(_16XFHI)
#undef _16XFHI
#endif

/* mlkem/native/x86_64/src/consts.h:20 */
#if defined(_16XMONTSQLO)
#undef _16XMONTSQLO
#endif

/* mlkem/native/x86_64/src/consts.h:21 */
#if defined(_16XMONTSQHI)
#undef _16XMONTSQHI
#endif

/* mlkem/native/x86_64/src/consts.h:22 */
#if defined(_16XMASK)
#undef _16XMASK
#endif

/* mlkem/native/x86_64/src/consts.h:23 */
#if defined(_REVIDXB)
#undef _REVIDXB
#endif

/* mlkem/native/x86_64/src/consts.h:24 */
#if defined(_REVIDXD)
#undef _REVIDXD
#endif

/* mlkem/native/x86_64/src/consts.h:25 */
#if defined(_ZETAS_EXP)
#undef _ZETAS_EXP
#endif

/* mlkem/native/x86_64/src/consts.h:26 */
#if defined(_16XSHIFT)
#undef _16XSHIFT
#endif

/* mlkem/native/x86_64/src/consts.h:39 */
#if defined(qdata)
#undef qdata
#endif

/* mlkem/native/x86_64/src/default_impl.h:10 */
#if defined(MLKEM_NATIVE_ARITH_PROFILE_IMPL_H)
#undef MLKEM_NATIVE_ARITH_PROFILE_IMPL_H
#endif

/* mlkem/native/x86_64/src/default_impl.h:18 */
#if defined(MLKEM_USE_NATIVE_NTT_CUSTOM_ORDER)
#undef MLKEM_USE_NATIVE_NTT_CUSTOM_ORDER
#endif

/* mlkem/native/x86_64/src/default_impl.h:20 */
#if defined(MLKEM_USE_NATIVE_REJ_UNIFORM)
#undef MLKEM_USE_NATIVE_REJ_UNIFORM
#endif

/* mlkem/native/x86_64/src/default_impl.h:21 */
#if defined(MLKEM_USE_NATIVE_NTT)
#undef MLKEM_USE_NATIVE_NTT
#endif

/* mlkem/native/x86_64/src/default_impl.h:22 */
#if defined(MLKEM_USE_NATIVE_INTT)
#undef MLKEM_USE_NATIVE_INTT
#endif

/* mlkem/native/x86_64/src/default_impl.h:23 */
#if defined(MLKEM_USE_NATIVE_POLY_REDUCE)
#undef MLKEM_USE_NATIVE_POLY_REDUCE
#endif

/* mlkem/native/x86_64/src/default_impl.h:24 */
#if defined(MLKEM_USE_NATIVE_POLY_TOMONT)
#undef MLKEM_USE_NATIVE_POLY_TOMONT
#endif

/* mlkem/native/x86_64/src/default_impl.h:25 */
#if defined(MLKEM_USE_NATIVE_POLYVEC_BASEMUL_ACC_MONTGOMERY_CACHED)
#undef MLKEM_USE_NATIVE_POLYVEC_BASEMUL_ACC_MONTGOMERY_CACHED
#endif

/* mlkem/native/x86_64/src/default_impl.h:26 */
#if defined(MLKEM_USE_NATIVE_POLY_MULCACHE_COMPUTE)
#undef MLKEM_USE_NATIVE_POLY_MULCACHE_COMPUTE
#endif

/* mlkem/native/x86_64/src/default_impl.h:27 */
#if defined(MLKEM_USE_NATIVE_POLY_TOBYTES)
#undef MLKEM_USE_NATIVE_POLY_TOBYTES
#endif

/* mlkem/native/x86_64/src/default_impl.h:28 */
#if defined(MLKEM_USE_NATIVE_POLY_FROMBYTES)
#undef MLKEM_USE_NATIVE_POLY_FROMBYTES
#endif

/* mlkem/native/x86_64/src/default_impl.h:30 */
#if defined(INVNTT_BOUND_NATIVE)
#undef INVNTT_BOUND_NATIVE
#endif

/* mlkem/native/x86_64/src/default_impl.h:31 */
#if defined(NTT_BOUND_NATIVE)
#undef NTT_BOUND_NATIVE
#endif

/* mlkem/native/x86_64/src/rej_uniform_avx2.c:20 */
#if defined(_mm256_cmpge_epu16)
#undef _mm256_cmpge_epu16
#endif

/* mlkem/native/x86_64/src/rej_uniform_avx2.c:21 */
#if defined(_mm_cmpge_epu16)
#undef _mm_cmpge_epu16
#endif

/* mlkem/native/x86_64/src/rej_uniform_avx2.c:130 */
#if defined(empty_cu_rej_uniform_avx2)
#undef empty_cu_rej_uniform_avx2
#endif

/* mlkem/native/x86_64/src/rej_uniform_table.c:155 */
#if defined(empty_cu_avx2_rej_uniform_table)
#undef empty_cu_avx2_rej_uniform_table
#endif

/* mlkem/ntt.c:156 */
#if defined(INVNTT_BOUND_REF)
#undef INVNTT_BOUND_REF
#endif

/* mlkem/ntt.h:5 */
#if defined(NTT_H)
#undef NTT_H
#endif

/* mlkem/ntt.h:13 */
#if defined(zetas)
#undef zetas
#endif

/* mlkem/ntt.h:16 */
#if defined(poly_ntt)
#undef poly_ntt
#endif

/* mlkem/ntt.h:42 */
#if defined(poly_invntt_tomont)
#undef poly_invntt_tomont
#endif

/* mlkem/ntt.h:66 */
#if defined(basemul_cached)
#undef basemul_cached
#endif

/* mlkem/params.h:5 */
#if defined(PARAMS_H)
#undef PARAMS_H
#endif

/* mlkem/params.h:13 */
#if defined(MLKEM_N)
#undef MLKEM_N
#endif

/* mlkem/params.h:14 */
#if defined(MLKEM_Q)
#undef MLKEM_Q
#endif

/* mlkem/params.h:15 */
#if defined(UINT12_MAX)
#undef UINT12_MAX
#endif

/* mlkem/params.h:17 */
#if defined(MLKEM_SYMBYTES)
#undef MLKEM_SYMBYTES
#endif

/* mlkem/params.h:18 */
#if defined(MLKEM_SSBYTES)
#undef MLKEM_SSBYTES
#endif

/* mlkem/params.h:20 */
#if defined(MLKEM_POLYBYTES)
#undef MLKEM_POLYBYTES
#endif

/* mlkem/params.h:21 */
#if defined(MLKEM_POLYVECBYTES)
#undef MLKEM_POLYVECBYTES
#endif

/* mlkem/params.h:24 */
#if defined(MLKEM_ETA1)
#undef MLKEM_ETA1
#endif

/* mlkem/params.h:25 */
#if defined(MLKEM_POLYCOMPRESSEDBYTES_DV)
#undef MLKEM_POLYCOMPRESSEDBYTES_DV
#endif

/* mlkem/params.h:26 */
#if defined(MLKEM_POLYCOMPRESSEDBYTES_DU)
#undef MLKEM_POLYCOMPRESSEDBYTES_DU
#endif

/* mlkem/params.h:27 */
#if defined(MLKEM_POLYVECCOMPRESSEDBYTES_DU)
#undef MLKEM_POLYVECCOMPRESSEDBYTES_DU
#endif

/* mlkem/params.h:29 */
#if defined(MLKEM_ETA1)
#undef MLKEM_ETA1
#endif

/* mlkem/params.h:30 */
#if defined(MLKEM_POLYCOMPRESSEDBYTES_DV)
#undef MLKEM_POLYCOMPRESSEDBYTES_DV
#endif

/* mlkem/params.h:31 */
#if defined(MLKEM_POLYCOMPRESSEDBYTES_DU)
#undef MLKEM_POLYCOMPRESSEDBYTES_DU
#endif

/* mlkem/params.h:32 */
#if defined(MLKEM_POLYVECCOMPRESSEDBYTES_DU)
#undef MLKEM_POLYVECCOMPRESSEDBYTES_DU
#endif

/* mlkem/params.h:34 */
#if defined(MLKEM_ETA1)
#undef MLKEM_ETA1
#endif

/* mlkem/params.h:35 */
#if defined(MLKEM_POLYCOMPRESSEDBYTES_DV)
#undef MLKEM_POLYCOMPRESSEDBYTES_DV
#endif

/* mlkem/params.h:36 */
#if defined(MLKEM_POLYCOMPRESSEDBYTES_DU)
#undef MLKEM_POLYCOMPRESSEDBYTES_DU
#endif

/* mlkem/params.h:37 */
#if defined(MLKEM_POLYVECCOMPRESSEDBYTES_DU)
#undef MLKEM_POLYVECCOMPRESSEDBYTES_DU
#endif

/* mlkem/params.h:40 */
#if defined(MLKEM_ETA2)
#undef MLKEM_ETA2
#endif

/* mlkem/params.h:42 */
#if defined(MLKEM_INDCPA_MSGBYTES)
#undef MLKEM_INDCPA_MSGBYTES
#endif

/* mlkem/params.h:43 */
#if defined(MLKEM_INDCPA_PUBLICKEYBYTES)
#undef MLKEM_INDCPA_PUBLICKEYBYTES
#endif

/* mlkem/params.h:44 */
#if defined(MLKEM_INDCPA_SECRETKEYBYTES)
#undef MLKEM_INDCPA_SECRETKEYBYTES
#endif

/* mlkem/params.h:45 */
#if defined(MLKEM_INDCPA_BYTES)
#undef MLKEM_INDCPA_BYTES
#endif

/* mlkem/params.h:48 */
#if defined(MLKEM_PUBLICKEYBYTES)
#undef MLKEM_PUBLICKEYBYTES
#endif

/* mlkem/params.h:50 */
#if defined(MLKEM_SECRETKEYBYTES)
#undef MLKEM_SECRETKEYBYTES
#endif

/* mlkem/params.h:53 */
#if defined(MLKEM_CIPHERTEXTBYTES)
#undef MLKEM_CIPHERTEXTBYTES
#endif

/* mlkem/params.h:55 */
#if defined(KECCAK_WAY)
#undef KECCAK_WAY
#endif

/* mlkem/poly.h:5 */
#if defined(POLY_H)
#undef POLY_H
#endif

/* mlkem/poly.h:15 */
#if defined(INVNTT_BOUND)
#undef INVNTT_BOUND
#endif

/* mlkem/poly.h:18 */
#if defined(NTT_BOUND)
#undef NTT_BOUND
#endif

/* mlkem/poly.h:24 */
#if defined(poly)
#undef poly
#endif

/* mlkem/poly.h:34 */
#if defined(poly_mulcache)
#undef poly_mulcache
#endif

/* mlkem/poly.h:307 */
#if defined(poly_compress_du)
#undef poly_compress_du
#endif

/* mlkem/poly.h:328 */
#if defined(poly_decompress_du)
#undef poly_decompress_du
#endif

/* mlkem/poly.h:351 */
#if defined(poly_compress_dv)
#undef poly_compress_dv
#endif

/* mlkem/poly.h:372 */
#if defined(poly_decompress_dv)
#undef poly_decompress_dv
#endif

/* mlkem/poly.h:396 */
#if defined(poly_tobytes)
#undef poly_tobytes
#endif

/* mlkem/poly.h:420 */
#if defined(poly_frombytes)
#undef poly_frombytes
#endif

/* mlkem/poly.h:443 */
#if defined(poly_frommsg)
#undef poly_frommsg
#endif

/* mlkem/poly.h:460 */
#if defined(poly_tomsg)
#undef poly_tomsg
#endif

/* mlkem/poly.h:478 */
#if defined(poly_getnoise_eta1_4x)
#undef poly_getnoise_eta1_4x
#endif

/* mlkem/poly.h:555 */
#if defined(poly_getnoise_eta2_4x)
#undef poly_getnoise_eta2_4x
#endif

/* mlkem/poly.h:558 */
#if defined(poly_getnoise_eta2)
#undef poly_getnoise_eta2
#endif

/* mlkem/poly.h:580 */
#if defined(poly_getnoise_eta1122_4x)
#undef poly_getnoise_eta1122_4x
#endif

/* mlkem/poly.h:609 */
#if defined(poly_basemul_montgomery_cached)
#undef poly_basemul_montgomery_cached
#endif

/* mlkem/poly.h:642 */
#if defined(poly_tomont)
#undef poly_tomont
#endif

/* mlkem/poly.h:660 */
#if defined(poly_mulcache_compute)
#undef poly_mulcache_compute
#endif

/* mlkem/poly.h:690 */
#if defined(poly_reduce)
#undef poly_reduce
#endif

/* mlkem/poly.h:715 */
#if defined(poly_add)
#undef poly_add
#endif

/* mlkem/poly.h:743 */
#if defined(poly_sub)
#undef poly_sub
#endif

/* mlkem/polyvec.h:5 */
#if defined(POLYVEC_H)
#undef POLYVEC_H
#endif

/* mlkem/polyvec.h:11 */
#if defined(polyvec)
#undef polyvec
#endif

/* mlkem/polyvec.h:17 */
#if defined(polyvec_mulcache)
#undef polyvec_mulcache
#endif

/* mlkem/polyvec.h:23 */
#if defined(polyvec_compress_du)
#undef polyvec_compress_du
#endif

/* mlkem/polyvec.h:45 */
#if defined(polyvec_decompress_du)
#undef polyvec_decompress_du
#endif

/* mlkem/polyvec.h:67 */
#if defined(polyvec_tobytes)
#undef polyvec_tobytes
#endif

/* mlkem/polyvec.h:87 */
#if defined(polyvec_frombytes)
#undef polyvec_frombytes
#endif

/* mlkem/polyvec.h:108 */
#if defined(polyvec_ntt)
#undef polyvec_ntt
#endif

/* mlkem/polyvec.h:133 */
#if defined(polyvec_invntt_tomont)
#undef polyvec_invntt_tomont
#endif

/* mlkem/polyvec.h:157 */
#if defined(polyvec_basemul_acc_montgomery)
#undef polyvec_basemul_acc_montgomery
#endif

/* mlkem/polyvec.h:180 */
#if defined(polyvec_basemul_acc_montgomery_cached)
#undef polyvec_basemul_acc_montgomery_cached
#endif

/* mlkem/polyvec.h:212 */
#if defined(polyvec_mulcache_compute)
#undef polyvec_mulcache_compute
#endif

/* mlkem/polyvec.h:245 */
#if defined(polyvec_reduce)
#undef polyvec_reduce
#endif

/* mlkem/polyvec.h:270 */
#if defined(polyvec_add)
#undef polyvec_add
#endif

/* mlkem/polyvec.h:300 */
#if defined(polyvec_tomont)
#undef polyvec_tomont
#endif

/* mlkem/randombytes.h:5 */
#if defined(RANDOMBYTES_H)
#undef RANDOMBYTES_H
#endif

/* mlkem/reduce.h:5 */
#if defined(REDUCE_H)
#undef REDUCE_H
#endif

/* mlkem/reduce.h:12 */
#if defined(HALF_Q)
#undef HALF_Q
#endif

/* mlkem/rej_uniform.h:5 */
#if defined(REJ_UNIFORM_H)
#undef REJ_UNIFORM_H
#endif

/* mlkem/rej_uniform.h:12 */
#if defined(rej_uniform)
#undef rej_uniform
#endif

/* mlkem/symmetric.h:5 */
#if defined(SYMMETRIC_H)
#undef SYMMETRIC_H
#endif

/* mlkem/symmetric.h:16 */
#if defined(hash_h)
#undef hash_h
#endif

/* mlkem/symmetric.h:19 */
#if defined(hash_g)
#undef hash_g
#endif

/* mlkem/symmetric.h:22 */
#if defined(hash_j)
#undef hash_j
#endif

/* mlkem/symmetric.h:26 */
#if defined(prf_eta)
#undef prf_eta
#endif

/* mlkem/symmetric.h:28 */
#if defined(prf_eta1)
#undef prf_eta1
#endif

/* mlkem/symmetric.h:29 */
#if defined(prf_eta2)
#undef prf_eta2
#endif

/* mlkem/symmetric.h:30 */
#if defined(prf_eta1_x4)
#undef prf_eta1_x4
#endif

/* mlkem/symmetric.h:35 */
#if defined(xof_ctx)
#undef xof_ctx
#endif

/* mlkem/symmetric.h:36 */
#if defined(xof_x4_ctx)
#undef xof_x4_ctx
#endif

/* mlkem/symmetric.h:37 */
#if defined(xof_absorb)
#undef xof_absorb
#endif

/* mlkem/symmetric.h:39 */
#if defined(xof_squeezeblocks)
#undef xof_squeezeblocks
#endif

/* mlkem/symmetric.h:41 */
#if defined(xof_release)
#undef xof_release
#endif

/* mlkem/symmetric.h:43 */
#if defined(xof_x4_absorb)
#undef xof_x4_absorb
#endif

/* mlkem/symmetric.h:45 */
#if defined(xof_x4_squeezeblocks)
#undef xof_x4_squeezeblocks
#endif

/* mlkem/symmetric.h:47 */
#if defined(xof_x4_release)
#undef xof_x4_release
#endif

/* mlkem/symmetric.h:49 */
#if defined(XOF_RATE)
#undef XOF_RATE
#endif

/* mlkem/sys.h:5 */
#if defined(MLKEM_NATIVE_SYS_H)
#undef MLKEM_NATIVE_SYS_H
#endif

/* mlkem/sys.h:10 */
#if defined(SYS_AARCH64)
#undef SYS_AARCH64
#endif

/* mlkem/sys.h:15 */
#if defined(SYS_AARCH64_EB)
#undef SYS_AARCH64_EB
#endif

/* mlkem/sys.h:19 */
#if defined(SYS_X86_64)
#undef SYS_X86_64
#endif

/* mlkem/sys.h:21 */
#if defined(SYS_X86_64_AVX2)
#undef SYS_X86_64_AVX2
#endif

/* mlkem/sys.h:29 */
#if defined(SYS_LITTLE_ENDIAN)
#undef SYS_LITTLE_ENDIAN
#endif

/* mlkem/sys.h:31 */
#if defined(SYS_BIG_ENDIAN)
#undef SYS_BIG_ENDIAN
#endif

/* mlkem/sys.h:65 */
#if defined(INLINE)
#undef INLINE
#endif

/* mlkem/sys.h:66 */
#if defined(ALWAYS_INLINE)
#undef ALWAYS_INLINE
#endif

/* mlkem/sys.h:68 */
#if defined(INLINE)
#undef INLINE
#endif

/* mlkem/sys.h:69 */
#if defined(ALWAYS_INLINE)
#undef ALWAYS_INLINE
#endif

/* mlkem/sys.h:71 */
#if defined(INLINE)
#undef INLINE
#endif

/* mlkem/sys.h:72 */
#if defined(ALWAYS_INLINE)
#undef ALWAYS_INLINE
#endif

/* mlkem/sys.h:76 */
#if defined(INLINE)
#undef INLINE
#endif

/* mlkem/sys.h:77 */
#if defined(ALWAYS_INLINE)
#undef ALWAYS_INLINE
#endif

/* mlkem/sys.h:86 */
#if defined(RESTRICT)
#undef RESTRICT
#endif

/* mlkem/sys.h:88 */
#if defined(RESTRICT)
#undef RESTRICT
#endif

/* mlkem/sys.h:93 */
#if defined(RESTRICT)
#undef RESTRICT
#endif

/* mlkem/sys.h:96 */
#if defined(DEFAULT_ALIGN)
#undef DEFAULT_ALIGN
#endif

/* mlkem/sys.h:98 */
#if defined(ALIGN)
#undef ALIGN
#endif

/* mlkem/sys.h:99 */
#if defined(asm)
#undef asm
#endif

/* mlkem/sys.h:101 */
#if defined(asm)
#undef asm
#endif

/* mlkem/sys.h:102 */
#if defined(ALIGN)
#undef ALIGN
#endif

/* mlkem/verify.c:16 */
#if defined(empty_cu_verify)
#undef empty_cu_verify
#endif

/* mlkem/verify.h:5 */
#if defined(VERIFY_H)
#undef VERIFY_H
#endif

/* mlkem/verify.h:47 */
#if defined(MLKEM_USE_ASM_VALUE_BARRIER)
#undef MLKEM_USE_ASM_VALUE_BARRIER
#endif

/* mlkem/verify.h:56 */
#if defined(ct_opt_blocker_u64)
#undef ct_opt_blocker_u64
#endif
