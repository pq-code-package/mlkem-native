/*
 * Copyright (c) 2024 The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0
 */

/*
 * WARNING: This file is auto-generated from scripts/autogen
 *          Do not modify it directly.
 */

/*
 * Monolithic assembly file bundling all assembly files within mlkem-native
 */

#include "mlkem/native/aarch64/src/intt_clean.S"

/*
 * Undo all #define directives from mlkem/native/aarch64/src/intt_clean.S
 */

/* mlkem/native/aarch64/src/intt_clean.S */
#if defined(barrett_reduce)
#undef barrett_reduce
#endif

/* mlkem/native/aarch64/src/intt_clean.S */
#if defined(dup8h)
#undef dup8h
#endif

/* mlkem/native/aarch64/src/intt_clean.S */
#if defined(gs_butterfly)
#undef gs_butterfly
#endif

/* mlkem/native/aarch64/src/intt_clean.S */
#if defined(gs_butterfly_v)
#undef gs_butterfly_v
#endif

/* mlkem/native/aarch64/src/intt_clean.S */
#if defined(load_next_roots_34)
#undef load_next_roots_34
#endif

/* mlkem/native/aarch64/src/intt_clean.S */
#if defined(load_next_roots_56)
#undef load_next_roots_56
#endif

/* mlkem/native/aarch64/src/intt_clean.S */
#if defined(load_roots_012)
#undef load_roots_012
#endif

/* mlkem/native/aarch64/src/intt_clean.S */
#if defined(mul_ninv)
#undef mul_ninv
#endif

/* mlkem/native/aarch64/src/intt_clean.S */
#if defined(mulmod)
#undef mulmod
#endif

/* mlkem/native/aarch64/src/intt_clean.S */
#if defined(mulmodq)
#undef mulmodq
#endif

/* mlkem/native/aarch64/src/intt_clean.S */
#if defined(pop_stack)
#undef pop_stack
#endif

/* mlkem/native/aarch64/src/intt_clean.S */
#if defined(push_stack)
#undef push_stack
#endif

/* mlkem/native/aarch64/src/intt_clean.S */
#if defined(restore_vregs)
#undef restore_vregs
#endif

/* mlkem/native/aarch64/src/intt_clean.S */
#if defined(save_vregs)
#undef save_vregs
#endif

/* mlkem/native/aarch64/src/intt_clean.S */
#if defined(transpose4)
#undef transpose4
#endif

/* mlkem/native/aarch64/src/intt_clean.S */
#if defined(transpose_single)
#undef transpose_single
#endif

#include "mlkem/native/aarch64/src/intt_opt.S"

/*
 * Undo all #define directives from mlkem/native/aarch64/src/intt_opt.S
 */

/* mlkem/native/aarch64/src/intt_opt.S */
#if defined(barrett_reduce)
#undef barrett_reduce
#endif

/* mlkem/native/aarch64/src/intt_opt.S */
#if defined(dup8h)
#undef dup8h
#endif

/* mlkem/native/aarch64/src/intt_opt.S */
#if defined(gs_butterfly)
#undef gs_butterfly
#endif

/* mlkem/native/aarch64/src/intt_opt.S */
#if defined(gs_butterfly_v)
#undef gs_butterfly_v
#endif

/* mlkem/native/aarch64/src/intt_opt.S */
#if defined(load_next_roots_34)
#undef load_next_roots_34
#endif

/* mlkem/native/aarch64/src/intt_opt.S */
#if defined(load_next_roots_56)
#undef load_next_roots_56
#endif

/* mlkem/native/aarch64/src/intt_opt.S */
#if defined(load_roots_012)
#undef load_roots_012
#endif

/* mlkem/native/aarch64/src/intt_opt.S */
#if defined(mul_ninv)
#undef mul_ninv
#endif

/* mlkem/native/aarch64/src/intt_opt.S */
#if defined(mulmod)
#undef mulmod
#endif

/* mlkem/native/aarch64/src/intt_opt.S */
#if defined(mulmodq)
#undef mulmodq
#endif

/* mlkem/native/aarch64/src/intt_opt.S */
#if defined(pop_stack)
#undef pop_stack
#endif

/* mlkem/native/aarch64/src/intt_opt.S */
#if defined(push_stack)
#undef push_stack
#endif

/* mlkem/native/aarch64/src/intt_opt.S */
#if defined(restore_vregs)
#undef restore_vregs
#endif

/* mlkem/native/aarch64/src/intt_opt.S */
#if defined(save_vregs)
#undef save_vregs
#endif

/* mlkem/native/aarch64/src/intt_opt.S */
#if defined(transpose4)
#undef transpose4
#endif

/* mlkem/native/aarch64/src/intt_opt.S */
#if defined(transpose_single)
#undef transpose_single
#endif

#include "mlkem/native/aarch64/src/ntt_clean.S"

/*
 * Undo all #define directives from mlkem/native/aarch64/src/ntt_clean.S
 */

/* mlkem/native/aarch64/src/ntt_clean.S */
#if defined(ct_butterfly)
#undef ct_butterfly
#endif

/* mlkem/native/aarch64/src/ntt_clean.S */
#if defined(ct_butterfly_v)
#undef ct_butterfly_v
#endif

/* mlkem/native/aarch64/src/ntt_clean.S */
#if defined(load_next_roots_34)
#undef load_next_roots_34
#endif

/* mlkem/native/aarch64/src/ntt_clean.S */
#if defined(load_next_roots_56)
#undef load_next_roots_56
#endif

/* mlkem/native/aarch64/src/ntt_clean.S */
#if defined(load_roots_012)
#undef load_roots_012
#endif

/* mlkem/native/aarch64/src/ntt_clean.S */
#if defined(mulmod)
#undef mulmod
#endif

/* mlkem/native/aarch64/src/ntt_clean.S */
#if defined(mulmodq)
#undef mulmodq
#endif

/* mlkem/native/aarch64/src/ntt_clean.S */
#if defined(pop_stack)
#undef pop_stack
#endif

/* mlkem/native/aarch64/src/ntt_clean.S */
#if defined(push_stack)
#undef push_stack
#endif

/* mlkem/native/aarch64/src/ntt_clean.S */
#if defined(restore_vregs)
#undef restore_vregs
#endif

/* mlkem/native/aarch64/src/ntt_clean.S */
#if defined(save_vregs)
#undef save_vregs
#endif

/* mlkem/native/aarch64/src/ntt_clean.S */
#if defined(transpose4)
#undef transpose4
#endif

#include "mlkem/native/aarch64/src/ntt_opt.S"

/*
 * Undo all #define directives from mlkem/native/aarch64/src/ntt_opt.S
 */

/* mlkem/native/aarch64/src/ntt_opt.S */
#if defined(ct_butterfly)
#undef ct_butterfly
#endif

/* mlkem/native/aarch64/src/ntt_opt.S */
#if defined(ct_butterfly_v)
#undef ct_butterfly_v
#endif

/* mlkem/native/aarch64/src/ntt_opt.S */
#if defined(load_next_roots_34)
#undef load_next_roots_34
#endif

/* mlkem/native/aarch64/src/ntt_opt.S */
#if defined(load_next_roots_56)
#undef load_next_roots_56
#endif

/* mlkem/native/aarch64/src/ntt_opt.S */
#if defined(load_roots_012)
#undef load_roots_012
#endif

/* mlkem/native/aarch64/src/ntt_opt.S */
#if defined(mulmod)
#undef mulmod
#endif

/* mlkem/native/aarch64/src/ntt_opt.S */
#if defined(mulmodq)
#undef mulmodq
#endif

/* mlkem/native/aarch64/src/ntt_opt.S */
#if defined(pop_stack)
#undef pop_stack
#endif

/* mlkem/native/aarch64/src/ntt_opt.S */
#if defined(push_stack)
#undef push_stack
#endif

/* mlkem/native/aarch64/src/ntt_opt.S */
#if defined(restore_vregs)
#undef restore_vregs
#endif

/* mlkem/native/aarch64/src/ntt_opt.S */
#if defined(save_vregs)
#undef save_vregs
#endif

/* mlkem/native/aarch64/src/ntt_opt.S */
#if defined(transpose4)
#undef transpose4
#endif

#include "mlkem/native/aarch64/src/poly_clean.S"

/*
 * Undo all #define directives from mlkem/native/aarch64/src/poly_clean.S
 */

/* mlkem/native/aarch64/src/poly_clean.S */
#if defined(barrett_reduce)
#undef barrett_reduce
#endif

/* mlkem/native/aarch64/src/poly_clean.S */
#if defined(dup8h)
#undef dup8h
#endif

/* mlkem/native/aarch64/src/poly_clean.S */
#if defined(mulmod)
#undef mulmod
#endif

/* mlkem/native/aarch64/src/poly_clean.S */
#if defined(scalar_signed_to_unsigned)
#undef scalar_signed_to_unsigned
#endif

#include "mlkem/native/aarch64/src/poly_opt.S"

/*
 * Undo all #define directives from mlkem/native/aarch64/src/poly_opt.S
 */

/* mlkem/native/aarch64/src/poly_opt.S */
#if defined(barrett_reduce)
#undef barrett_reduce
#endif

/* mlkem/native/aarch64/src/poly_opt.S */
#if defined(dup8h)
#undef dup8h
#endif

/* mlkem/native/aarch64/src/poly_opt.S */
#if defined(mulmod)
#undef mulmod
#endif

/* mlkem/native/aarch64/src/poly_opt.S */
#if defined(scalar_signed_to_unsigned)
#undef scalar_signed_to_unsigned
#endif

#include "mlkem/native/aarch64/src/polyvec_clean.S"

/*
 * Undo all #define directives from mlkem/native/aarch64/src/polyvec_clean.S
 */

/* mlkem/native/aarch64/src/polyvec_clean.S */
#if defined(dup8h)
#undef dup8h
#endif

/* mlkem/native/aarch64/src/polyvec_clean.S */
#if defined(ld2_wrap)
#undef ld2_wrap
#endif

/* mlkem/native/aarch64/src/polyvec_clean.S */
#if defined(load_polys)
#undef load_polys
#endif

/* mlkem/native/aarch64/src/polyvec_clean.S */
#if defined(montgomery_reduce_long)
#undef montgomery_reduce_long
#endif

/* mlkem/native/aarch64/src/polyvec_clean.S */
#if defined(pmlal)
#undef pmlal
#endif

/* mlkem/native/aarch64/src/polyvec_clean.S */
#if defined(pmull)
#undef pmull
#endif

/* mlkem/native/aarch64/src/polyvec_clean.S */
#if defined(pop_stack)
#undef pop_stack
#endif

/* mlkem/native/aarch64/src/polyvec_clean.S */
#if defined(push_stack)
#undef push_stack
#endif

/* mlkem/native/aarch64/src/polyvec_clean.S */
#if defined(restore_vregs)
#undef restore_vregs
#endif

/* mlkem/native/aarch64/src/polyvec_clean.S */
#if defined(save_vregs)
#undef save_vregs
#endif

/* mlkem/native/aarch64/src/polyvec_clean.S */
#if defined(st2_wrap)
#undef st2_wrap
#endif

#include "mlkem/native/aarch64/src/polyvec_opt.S"

/*
 * Undo all #define directives from mlkem/native/aarch64/src/polyvec_opt.S
 */

/* mlkem/native/aarch64/src/polyvec_opt.S */
#if defined(dup8h)
#undef dup8h
#endif

/* mlkem/native/aarch64/src/polyvec_opt.S */
#if defined(ld2_wrap)
#undef ld2_wrap
#endif

/* mlkem/native/aarch64/src/polyvec_opt.S */
#if defined(load_polys)
#undef load_polys
#endif

/* mlkem/native/aarch64/src/polyvec_opt.S */
#if defined(montgomery_reduce_long)
#undef montgomery_reduce_long
#endif

/* mlkem/native/aarch64/src/polyvec_opt.S */
#if defined(pmlal)
#undef pmlal
#endif

/* mlkem/native/aarch64/src/polyvec_opt.S */
#if defined(pmull)
#undef pmull
#endif

/* mlkem/native/aarch64/src/polyvec_opt.S */
#if defined(pop_stack)
#undef pop_stack
#endif

/* mlkem/native/aarch64/src/polyvec_opt.S */
#if defined(push_stack)
#undef push_stack
#endif

/* mlkem/native/aarch64/src/polyvec_opt.S */
#if defined(restore_vregs)
#undef restore_vregs
#endif

/* mlkem/native/aarch64/src/polyvec_opt.S */
#if defined(save_vregs)
#undef save_vregs
#endif

/* mlkem/native/aarch64/src/polyvec_opt.S */
#if defined(st2_wrap)
#undef st2_wrap
#endif

#include "mlkem/native/aarch64/src/rej_uniform_asm_clean.S"

/*
 * Undo all #define directives from
 * mlkem/native/aarch64/src/rej_uniform_asm_clean.S
 */

/* mlkem/native/aarch64/src/rej_uniform_asm_clean.S */
#if defined(STACK_OFFSET_TMP_OUTPUT)
#undef STACK_OFFSET_TMP_OUTPUT
#endif

/* mlkem/native/aarch64/src/rej_uniform_asm_clean.S */
#if defined(STACK_SIZE)
#undef STACK_SIZE
#endif

/* mlkem/native/aarch64/src/rej_uniform_asm_clean.S */
#if defined(pop_stack)
#undef pop_stack
#endif

/* mlkem/native/aarch64/src/rej_uniform_asm_clean.S */
#if defined(push_stack)
#undef push_stack
#endif

#include "mlkem/native/x86_64/src/basemul.S"

/*
 * Undo all #define directives from mlkem/native/x86_64/src/basemul.S
 */

/* mlkem/native/x86_64/src/basemul.S */
#if defined(schoolbook)
#undef schoolbook
#endif

#include "mlkem/native/x86_64/src/fq.S"

/*
 * Undo all #define directives from mlkem/native/x86_64/src/fq.S
 */

#include "mlkem/native/x86_64/src/intt.S"

/*
 * Undo all #define directives from mlkem/native/x86_64/src/intt.S
 */

/* mlkem/native/x86_64/src/intt.S */
#if defined(butterfly)
#undef butterfly
#endif

/* mlkem/native/x86_64/src/intt.S */
#if defined(intt_level6)
#undef intt_level6
#endif

/* mlkem/native/x86_64/src/intt.S */
#if defined(intt_levels0t5)
#undef intt_levels0t5
#endif

#include "mlkem/native/x86_64/src/ntt.S"

/*
 * Undo all #define directives from mlkem/native/x86_64/src/ntt.S
 */

/* mlkem/native/x86_64/src/ntt.S */
#if defined(level0)
#undef level0
#endif

/* mlkem/native/x86_64/src/ntt.S */
#if defined(levels1t6)
#undef levels1t6
#endif

/* mlkem/native/x86_64/src/ntt.S */
#if defined(mul)
#undef mul
#endif

/* mlkem/native/x86_64/src/ntt.S */
#if defined(reduce)
#undef reduce
#endif

/* mlkem/native/x86_64/src/ntt.S */
#if defined(update)
#undef update
#endif

#include "mlkem/native/x86_64/src/shuffle.S"

/*
 * Undo all #define directives from mlkem/native/x86_64/src/shuffle.S
 */


#if !defined(MLKEM_NATIVE_MONOBUILD_NO_FIPS202_SOURCES)
#include "mlkem/fips202/native/aarch64/src/keccak_f1600_x1_scalar_asm_opt.S"

/*
 * Undo all #define directives from
 * mlkem/fips202/native/aarch64/src/keccak_f1600_x1_scalar_asm_opt.S
 */

/* mlkem/fips202/native/aarch64/src/keccak_f1600_x1_scalar_asm_opt.S */
#if defined(KECCAK_F1600_ROUNDS)
#undef KECCAK_F1600_ROUNDS
#endif

/* mlkem/fips202/native/aarch64/src/keccak_f1600_x1_scalar_asm_opt.S */
#if defined(STACK_BASE_GPRS)
#undef STACK_BASE_GPRS
#endif

/* mlkem/fips202/native/aarch64/src/keccak_f1600_x1_scalar_asm_opt.S */
#if defined(STACK_LOCS)
#undef STACK_LOCS
#endif

/* mlkem/fips202/native/aarch64/src/keccak_f1600_x1_scalar_asm_opt.S */
#if defined(STACK_LOC_CONST)
#undef STACK_LOC_CONST
#endif

/* mlkem/fips202/native/aarch64/src/keccak_f1600_x1_scalar_asm_opt.S */
#if defined(STACK_LOC_COUNT)
#undef STACK_LOC_COUNT
#endif

/* mlkem/fips202/native/aarch64/src/keccak_f1600_x1_scalar_asm_opt.S */
#if defined(STACK_LOC_INPUT)
#undef STACK_LOC_INPUT
#endif

/* mlkem/fips202/native/aarch64/src/keccak_f1600_x1_scalar_asm_opt.S */
#if defined(STACK_LOC_MISC0)
#undef STACK_LOC_MISC0
#endif

/* mlkem/fips202/native/aarch64/src/keccak_f1600_x1_scalar_asm_opt.S */
#if defined(STACK_SIZE)
#undef STACK_SIZE
#endif

/* mlkem/fips202/native/aarch64/src/keccak_f1600_x1_scalar_asm_opt.S */
#if defined(alloc_stack)
#undef alloc_stack
#endif

/* mlkem/fips202/native/aarch64/src/keccak_f1600_x1_scalar_asm_opt.S */
#if defined(final_rotate)
#undef final_rotate
#endif

/* mlkem/fips202/native/aarch64/src/keccak_f1600_x1_scalar_asm_opt.S */
#if defined(free_stack)
#undef free_stack
#endif

/* mlkem/fips202/native/aarch64/src/keccak_f1600_x1_scalar_asm_opt.S */
#if defined(load_state)
#undef load_state
#endif

/* mlkem/fips202/native/aarch64/src/keccak_f1600_x1_scalar_asm_opt.S */
#if defined(restore_gprs)
#undef restore_gprs
#endif

/* mlkem/fips202/native/aarch64/src/keccak_f1600_x1_scalar_asm_opt.S */
#if defined(save_gprs)
#undef save_gprs
#endif

/* mlkem/fips202/native/aarch64/src/keccak_f1600_x1_scalar_asm_opt.S */
#if defined(store_state)
#undef store_state
#endif

#include "mlkem/fips202/native/aarch64/src/keccak_f1600_x1_v84a_asm_clean.S"

/*
 * Undo all #define directives from
 * mlkem/fips202/native/aarch64/src/keccak_f1600_x1_v84a_asm_clean.S
 */

/* mlkem/fips202/native/aarch64/src/keccak_f1600_x1_v84a_asm_clean.S */
#if defined(KECCAK_F1600_ROUNDS)
#undef KECCAK_F1600_ROUNDS
#endif

/* mlkem/fips202/native/aarch64/src/keccak_f1600_x1_v84a_asm_clean.S */
#if defined(STACK_BASE_GPRS)
#undef STACK_BASE_GPRS
#endif

/* mlkem/fips202/native/aarch64/src/keccak_f1600_x1_v84a_asm_clean.S */
#if defined(STACK_SIZE)
#undef STACK_SIZE
#endif

/* mlkem/fips202/native/aarch64/src/keccak_f1600_x1_v84a_asm_clean.S */
#if defined(alloc_stack)
#undef alloc_stack
#endif

/* mlkem/fips202/native/aarch64/src/keccak_f1600_x1_v84a_asm_clean.S */
#if defined(bcax_m0)
#undef bcax_m0
#endif

/* mlkem/fips202/native/aarch64/src/keccak_f1600_x1_v84a_asm_clean.S */
#if defined(eor3_m0)
#undef eor3_m0
#endif

/* mlkem/fips202/native/aarch64/src/keccak_f1600_x1_v84a_asm_clean.S */
#if defined(free_stack)
#undef free_stack
#endif

/* mlkem/fips202/native/aarch64/src/keccak_f1600_x1_v84a_asm_clean.S */
#if defined(keccak_f1600_round)
#undef keccak_f1600_round
#endif

/* mlkem/fips202/native/aarch64/src/keccak_f1600_x1_v84a_asm_clean.S */
#if defined(load_input)
#undef load_input
#endif

/* mlkem/fips202/native/aarch64/src/keccak_f1600_x1_v84a_asm_clean.S */
#if defined(rax1_m0)
#undef rax1_m0
#endif

/* mlkem/fips202/native/aarch64/src/keccak_f1600_x1_v84a_asm_clean.S */
#if defined(restore_vregs)
#undef restore_vregs
#endif

/* mlkem/fips202/native/aarch64/src/keccak_f1600_x1_v84a_asm_clean.S */
#if defined(save_vregs)
#undef save_vregs
#endif

/* mlkem/fips202/native/aarch64/src/keccak_f1600_x1_v84a_asm_clean.S */
#if defined(store_input)
#undef store_input
#endif

/* mlkem/fips202/native/aarch64/src/keccak_f1600_x1_v84a_asm_clean.S */
#if defined(xar_m0)
#undef xar_m0
#endif

#include "mlkem/fips202/native/aarch64/src/keccak_f1600_x2_v84a_asm_clean.S"

/*
 * Undo all #define directives from
 * mlkem/fips202/native/aarch64/src/keccak_f1600_x2_v84a_asm_clean.S
 */

/* mlkem/fips202/native/aarch64/src/keccak_f1600_x2_v84a_asm_clean.S */
#if defined(KECCAK_F1600_ROUNDS)
#undef KECCAK_F1600_ROUNDS
#endif

/* mlkem/fips202/native/aarch64/src/keccak_f1600_x2_v84a_asm_clean.S */
#if defined(STACK_BASE_GPRS)
#undef STACK_BASE_GPRS
#endif

/* mlkem/fips202/native/aarch64/src/keccak_f1600_x2_v84a_asm_clean.S */
#if defined(STACK_SIZE)
#undef STACK_SIZE
#endif

/* mlkem/fips202/native/aarch64/src/keccak_f1600_x2_v84a_asm_clean.S */
#if defined(alloc_stack)
#undef alloc_stack
#endif

/* mlkem/fips202/native/aarch64/src/keccak_f1600_x2_v84a_asm_clean.S */
#if defined(bcax_m0)
#undef bcax_m0
#endif

/* mlkem/fips202/native/aarch64/src/keccak_f1600_x2_v84a_asm_clean.S */
#if defined(eor3_m0)
#undef eor3_m0
#endif

/* mlkem/fips202/native/aarch64/src/keccak_f1600_x2_v84a_asm_clean.S */
#if defined(free_stack)
#undef free_stack
#endif

/* mlkem/fips202/native/aarch64/src/keccak_f1600_x2_v84a_asm_clean.S */
#if defined(keccak_f1600_round)
#undef keccak_f1600_round
#endif

/* mlkem/fips202/native/aarch64/src/keccak_f1600_x2_v84a_asm_clean.S */
#if defined(load_input)
#undef load_input
#endif

/* mlkem/fips202/native/aarch64/src/keccak_f1600_x2_v84a_asm_clean.S */
#if defined(rax1_m0)
#undef rax1_m0
#endif

/* mlkem/fips202/native/aarch64/src/keccak_f1600_x2_v84a_asm_clean.S */
#if defined(restore_vregs)
#undef restore_vregs
#endif

/* mlkem/fips202/native/aarch64/src/keccak_f1600_x2_v84a_asm_clean.S */
#if defined(save_vregs)
#undef save_vregs
#endif

/* mlkem/fips202/native/aarch64/src/keccak_f1600_x2_v84a_asm_clean.S */
#if defined(store_input)
#undef store_input
#endif

/* mlkem/fips202/native/aarch64/src/keccak_f1600_x2_v84a_asm_clean.S */
#if defined(xar_m0)
#undef xar_m0
#endif

#include "mlkem/fips202/native/aarch64/src/keccak_f1600_x2_v8a_v84a_asm_hybrid.S"

/*
 * Undo all #define directives from
 * mlkem/fips202/native/aarch64/src/keccak_f1600_x2_v8a_v84a_asm_hybrid.S
 */

/* mlkem/fips202/native/aarch64/src/keccak_f1600_x2_v8a_v84a_asm_hybrid.S */
#if defined(KECCAK_F1600_ROUNDS)
#undef KECCAK_F1600_ROUNDS
#endif

/* mlkem/fips202/native/aarch64/src/keccak_f1600_x2_v8a_v84a_asm_hybrid.S */
#if defined(STACK_BASE_GPRS)
#undef STACK_BASE_GPRS
#endif

/* mlkem/fips202/native/aarch64/src/keccak_f1600_x2_v8a_v84a_asm_hybrid.S */
#if defined(STACK_SIZE)
#undef STACK_SIZE
#endif

/* mlkem/fips202/native/aarch64/src/keccak_f1600_x2_v8a_v84a_asm_hybrid.S */
#if defined(alloc_stack)
#undef alloc_stack
#endif

/* mlkem/fips202/native/aarch64/src/keccak_f1600_x2_v8a_v84a_asm_hybrid.S */
#if defined(bcax_m0)
#undef bcax_m0
#endif

/* mlkem/fips202/native/aarch64/src/keccak_f1600_x2_v8a_v84a_asm_hybrid.S */
#if defined(bcax_m1)
#undef bcax_m1
#endif

/* mlkem/fips202/native/aarch64/src/keccak_f1600_x2_v8a_v84a_asm_hybrid.S */
#if defined(eor3_m0)
#undef eor3_m0
#endif

/* mlkem/fips202/native/aarch64/src/keccak_f1600_x2_v8a_v84a_asm_hybrid.S */
#if defined(eor3_m1)
#undef eor3_m1
#endif

/* mlkem/fips202/native/aarch64/src/keccak_f1600_x2_v8a_v84a_asm_hybrid.S */
#if defined(free_stack)
#undef free_stack
#endif

/* mlkem/fips202/native/aarch64/src/keccak_f1600_x2_v8a_v84a_asm_hybrid.S */
#if defined(hybrid_round)
#undef hybrid_round
#endif

/* mlkem/fips202/native/aarch64/src/keccak_f1600_x2_v8a_v84a_asm_hybrid.S */
#if defined(load_input)
#undef load_input
#endif

/* mlkem/fips202/native/aarch64/src/keccak_f1600_x2_v8a_v84a_asm_hybrid.S */
#if defined(rax1_m0)
#undef rax1_m0
#endif

/* mlkem/fips202/native/aarch64/src/keccak_f1600_x2_v8a_v84a_asm_hybrid.S */
#if defined(rax1_m1)
#undef rax1_m1
#endif

/* mlkem/fips202/native/aarch64/src/keccak_f1600_x2_v8a_v84a_asm_hybrid.S */
#if defined(restore_gprs)
#undef restore_gprs
#endif

/* mlkem/fips202/native/aarch64/src/keccak_f1600_x2_v8a_v84a_asm_hybrid.S */
#if defined(restore_vregs)
#undef restore_vregs
#endif

/* mlkem/fips202/native/aarch64/src/keccak_f1600_x2_v8a_v84a_asm_hybrid.S */
#if defined(save_gprs)
#undef save_gprs
#endif

/* mlkem/fips202/native/aarch64/src/keccak_f1600_x2_v8a_v84a_asm_hybrid.S */
#if defined(save_vregs)
#undef save_vregs
#endif

/* mlkem/fips202/native/aarch64/src/keccak_f1600_x2_v8a_v84a_asm_hybrid.S */
#if defined(store_input)
#undef store_input
#endif

/* mlkem/fips202/native/aarch64/src/keccak_f1600_x2_v8a_v84a_asm_hybrid.S */
#if defined(xar_m0)
#undef xar_m0
#endif

/* mlkem/fips202/native/aarch64/src/keccak_f1600_x2_v8a_v84a_asm_hybrid.S */
#if defined(xar_m1)
#undef xar_m1
#endif

#include "mlkem/fips202/native/aarch64/src/keccak_f1600_x4_scalar_v84a_asm_hybrid_opt.S"

/*
 * Undo all #define directives from
 * mlkem/fips202/native/aarch64/src/keccak_f1600_x4_scalar_v84a_asm_hybrid_opt.S
 */

/* mlkem/fips202/native/aarch64/src/keccak_f1600_x4_scalar_v84a_asm_hybrid_opt.S
 */
#if defined(KECCAK_F1600_ROUNDS)
#undef KECCAK_F1600_ROUNDS
#endif

/* mlkem/fips202/native/aarch64/src/keccak_f1600_x4_scalar_v84a_asm_hybrid_opt.S
 */
#if defined(STACK_BASE_GPRS)
#undef STACK_BASE_GPRS
#endif

/* mlkem/fips202/native/aarch64/src/keccak_f1600_x4_scalar_v84a_asm_hybrid_opt.S
 */
#if defined(STACK_BASE_VREGS)
#undef STACK_BASE_VREGS
#endif

/* mlkem/fips202/native/aarch64/src/keccak_f1600_x4_scalar_v84a_asm_hybrid_opt.S
 */
#if defined(STACK_LOCS)
#undef STACK_LOCS
#endif

/* mlkem/fips202/native/aarch64/src/keccak_f1600_x4_scalar_v84a_asm_hybrid_opt.S
 */
#if defined(STACK_LOC_0)
#undef STACK_LOC_0
#endif

/* mlkem/fips202/native/aarch64/src/keccak_f1600_x4_scalar_v84a_asm_hybrid_opt.S
 */
#if defined(STACK_LOC_1)
#undef STACK_LOC_1
#endif

/* mlkem/fips202/native/aarch64/src/keccak_f1600_x4_scalar_v84a_asm_hybrid_opt.S
 */
#if defined(STACK_OFFSET_CONST_SCALAR)
#undef STACK_OFFSET_CONST_SCALAR
#endif

/* mlkem/fips202/native/aarch64/src/keccak_f1600_x4_scalar_v84a_asm_hybrid_opt.S
 */
#if defined(STACK_OFFSET_CONST_VECTOR)
#undef STACK_OFFSET_CONST_VECTOR
#endif

/* mlkem/fips202/native/aarch64/src/keccak_f1600_x4_scalar_v84a_asm_hybrid_opt.S
 */
#if defined(STACK_OFFSET_COUNT)
#undef STACK_OFFSET_COUNT
#endif

/* mlkem/fips202/native/aarch64/src/keccak_f1600_x4_scalar_v84a_asm_hybrid_opt.S
 */
#if defined(STACK_OFFSET_INPUT)
#undef STACK_OFFSET_INPUT
#endif

/* mlkem/fips202/native/aarch64/src/keccak_f1600_x4_scalar_v84a_asm_hybrid_opt.S
 */
#if defined(STACK_OFFSET_LOCS)
#undef STACK_OFFSET_LOCS
#endif

/* mlkem/fips202/native/aarch64/src/keccak_f1600_x4_scalar_v84a_asm_hybrid_opt.S
 */
#if defined(STACK_OFFSET_OUTER)
#undef STACK_OFFSET_OUTER
#endif

/* mlkem/fips202/native/aarch64/src/keccak_f1600_x4_scalar_v84a_asm_hybrid_opt.S
 */
#if defined(STACK_SIZE)
#undef STACK_SIZE
#endif

/* mlkem/fips202/native/aarch64/src/keccak_f1600_x4_scalar_v84a_asm_hybrid_opt.S
 */
#if defined(alloc_stack)
#undef alloc_stack
#endif

/* mlkem/fips202/native/aarch64/src/keccak_f1600_x4_scalar_v84a_asm_hybrid_opt.S
 */
#if defined(bcax_m0)
#undef bcax_m0
#endif

/* mlkem/fips202/native/aarch64/src/keccak_f1600_x4_scalar_v84a_asm_hybrid_opt.S
 */
#if defined(bcax_m1)
#undef bcax_m1
#endif

/* mlkem/fips202/native/aarch64/src/keccak_f1600_x4_scalar_v84a_asm_hybrid_opt.S
 */
#if defined(chi_step_ror)
#undef chi_step_ror
#endif

/* mlkem/fips202/native/aarch64/src/keccak_f1600_x4_scalar_v84a_asm_hybrid_opt.S
 */
#if defined(chi_step_ror2)
#undef chi_step_ror2
#endif

/* mlkem/fips202/native/aarch64/src/keccak_f1600_x4_scalar_v84a_asm_hybrid_opt.S
 */
#if defined(eor3_m0)
#undef eor3_m0
#endif

/* mlkem/fips202/native/aarch64/src/keccak_f1600_x4_scalar_v84a_asm_hybrid_opt.S
 */
#if defined(eor3_m1)
#undef eor3_m1
#endif

/* mlkem/fips202/native/aarch64/src/keccak_f1600_x4_scalar_v84a_asm_hybrid_opt.S
 */
#if defined(eor5)
#undef eor5
#endif

/* mlkem/fips202/native/aarch64/src/keccak_f1600_x4_scalar_v84a_asm_hybrid_opt.S
 */
#if defined(final_scalar_rotate)
#undef final_scalar_rotate
#endif

/* mlkem/fips202/native/aarch64/src/keccak_f1600_x4_scalar_v84a_asm_hybrid_opt.S
 */
#if defined(free_stack)
#undef free_stack
#endif

/* mlkem/fips202/native/aarch64/src/keccak_f1600_x4_scalar_v84a_asm_hybrid_opt.S
 */
#if defined(load_input_scalar)
#undef load_input_scalar
#endif

/* mlkem/fips202/native/aarch64/src/keccak_f1600_x4_scalar_v84a_asm_hybrid_opt.S
 */
#if defined(load_input_vector)
#undef load_input_vector
#endif

/* mlkem/fips202/native/aarch64/src/keccak_f1600_x4_scalar_v84a_asm_hybrid_opt.S
 */
#if defined(rax1_m0)
#undef rax1_m0
#endif

/* mlkem/fips202/native/aarch64/src/keccak_f1600_x4_scalar_v84a_asm_hybrid_opt.S
 */
#if defined(rax1_m1)
#undef rax1_m1
#endif

/* mlkem/fips202/native/aarch64/src/keccak_f1600_x4_scalar_v84a_asm_hybrid_opt.S
 */
#if defined(restore_gprs)
#undef restore_gprs
#endif

/* mlkem/fips202/native/aarch64/src/keccak_f1600_x4_scalar_v84a_asm_hybrid_opt.S
 */
#if defined(restore_vregs)
#undef restore_vregs
#endif

/* mlkem/fips202/native/aarch64/src/keccak_f1600_x4_scalar_v84a_asm_hybrid_opt.S
 */
#if defined(save_gprs)
#undef save_gprs
#endif

/* mlkem/fips202/native/aarch64/src/keccak_f1600_x4_scalar_v84a_asm_hybrid_opt.S
 */
#if defined(save_vregs)
#undef save_vregs
#endif

/* mlkem/fips202/native/aarch64/src/keccak_f1600_x4_scalar_v84a_asm_hybrid_opt.S
 */
#if defined(scalar_round_initial)
#undef scalar_round_initial
#endif

/* mlkem/fips202/native/aarch64/src/keccak_f1600_x4_scalar_v84a_asm_hybrid_opt.S
 */
#if defined(scalar_round_noninitial)
#undef scalar_round_noninitial
#endif

/* mlkem/fips202/native/aarch64/src/keccak_f1600_x4_scalar_v84a_asm_hybrid_opt.S
 */
#if defined(store_input_scalar)
#undef store_input_scalar
#endif

/* mlkem/fips202/native/aarch64/src/keccak_f1600_x4_scalar_v84a_asm_hybrid_opt.S
 */
#if defined(store_input_vector)
#undef store_input_vector
#endif

/* mlkem/fips202/native/aarch64/src/keccak_f1600_x4_scalar_v84a_asm_hybrid_opt.S
 */
#if defined(vector_round)
#undef vector_round
#endif

/* mlkem/fips202/native/aarch64/src/keccak_f1600_x4_scalar_v84a_asm_hybrid_opt.S
 */
#if defined(xar_m0)
#undef xar_m0
#endif

/* mlkem/fips202/native/aarch64/src/keccak_f1600_x4_scalar_v84a_asm_hybrid_opt.S
 */
#if defined(xar_m1)
#undef xar_m1
#endif

#include "mlkem/fips202/native/aarch64/src/keccak_f1600_x4_v8a_scalar_hybrid_asm_opt.S"

/*
 * Undo all #define directives from
 * mlkem/fips202/native/aarch64/src/keccak_f1600_x4_v8a_scalar_hybrid_asm_opt.S
 */

/* mlkem/fips202/native/aarch64/src/keccak_f1600_x4_v8a_scalar_hybrid_asm_opt.S
 */
#if defined(KECCAK_F1600_ROUNDS)
#undef KECCAK_F1600_ROUNDS
#endif

/* mlkem/fips202/native/aarch64/src/keccak_f1600_x4_v8a_scalar_hybrid_asm_opt.S
 */
#if defined(STACK_BASE_GPRS)
#undef STACK_BASE_GPRS
#endif

/* mlkem/fips202/native/aarch64/src/keccak_f1600_x4_v8a_scalar_hybrid_asm_opt.S
 */
#if defined(STACK_BASE_VREGS)
#undef STACK_BASE_VREGS
#endif

/* mlkem/fips202/native/aarch64/src/keccak_f1600_x4_v8a_scalar_hybrid_asm_opt.S
 */
#if defined(STACK_LOCS)
#undef STACK_LOCS
#endif

/* mlkem/fips202/native/aarch64/src/keccak_f1600_x4_v8a_scalar_hybrid_asm_opt.S
 */
#if defined(STACK_LOC_0)
#undef STACK_LOC_0
#endif

/* mlkem/fips202/native/aarch64/src/keccak_f1600_x4_v8a_scalar_hybrid_asm_opt.S
 */
#if defined(STACK_LOC_1)
#undef STACK_LOC_1
#endif

/* mlkem/fips202/native/aarch64/src/keccak_f1600_x4_v8a_scalar_hybrid_asm_opt.S
 */
#if defined(STACK_OFFSET_CONST_SCALAR)
#undef STACK_OFFSET_CONST_SCALAR
#endif

/* mlkem/fips202/native/aarch64/src/keccak_f1600_x4_v8a_scalar_hybrid_asm_opt.S
 */
#if defined(STACK_OFFSET_CONST_VECTOR)
#undef STACK_OFFSET_CONST_VECTOR
#endif

/* mlkem/fips202/native/aarch64/src/keccak_f1600_x4_v8a_scalar_hybrid_asm_opt.S
 */
#if defined(STACK_OFFSET_COUNT)
#undef STACK_OFFSET_COUNT
#endif

/* mlkem/fips202/native/aarch64/src/keccak_f1600_x4_v8a_scalar_hybrid_asm_opt.S
 */
#if defined(STACK_OFFSET_INPUT)
#undef STACK_OFFSET_INPUT
#endif

/* mlkem/fips202/native/aarch64/src/keccak_f1600_x4_v8a_scalar_hybrid_asm_opt.S
 */
#if defined(STACK_OFFSET_LOCS)
#undef STACK_OFFSET_LOCS
#endif

/* mlkem/fips202/native/aarch64/src/keccak_f1600_x4_v8a_scalar_hybrid_asm_opt.S
 */
#if defined(STACK_OFFSET_OUTER)
#undef STACK_OFFSET_OUTER
#endif

/* mlkem/fips202/native/aarch64/src/keccak_f1600_x4_v8a_scalar_hybrid_asm_opt.S
 */
#if defined(STACK_SIZE)
#undef STACK_SIZE
#endif

/* mlkem/fips202/native/aarch64/src/keccak_f1600_x4_v8a_scalar_hybrid_asm_opt.S
 */
#if defined(alloc_stack)
#undef alloc_stack
#endif

/* mlkem/fips202/native/aarch64/src/keccak_f1600_x4_v8a_scalar_hybrid_asm_opt.S
 */
#if defined(bcax_m1)
#undef bcax_m1
#endif

/* mlkem/fips202/native/aarch64/src/keccak_f1600_x4_v8a_scalar_hybrid_asm_opt.S
 */
#if defined(chi_step_ror)
#undef chi_step_ror
#endif

/* mlkem/fips202/native/aarch64/src/keccak_f1600_x4_v8a_scalar_hybrid_asm_opt.S
 */
#if defined(chi_step_ror2)
#undef chi_step_ror2
#endif

/* mlkem/fips202/native/aarch64/src/keccak_f1600_x4_v8a_scalar_hybrid_asm_opt.S
 */
#if defined(eor3_m1)
#undef eor3_m1
#endif

/* mlkem/fips202/native/aarch64/src/keccak_f1600_x4_v8a_scalar_hybrid_asm_opt.S
 */
#if defined(eor5)
#undef eor5
#endif

/* mlkem/fips202/native/aarch64/src/keccak_f1600_x4_v8a_scalar_hybrid_asm_opt.S
 */
#if defined(final_scalar_rotate)
#undef final_scalar_rotate
#endif

/* mlkem/fips202/native/aarch64/src/keccak_f1600_x4_v8a_scalar_hybrid_asm_opt.S
 */
#if defined(free_stack)
#undef free_stack
#endif

/* mlkem/fips202/native/aarch64/src/keccak_f1600_x4_v8a_scalar_hybrid_asm_opt.S
 */
#if defined(load_input_scalar)
#undef load_input_scalar
#endif

/* mlkem/fips202/native/aarch64/src/keccak_f1600_x4_v8a_scalar_hybrid_asm_opt.S
 */
#if defined(load_input_vector)
#undef load_input_vector
#endif

/* mlkem/fips202/native/aarch64/src/keccak_f1600_x4_v8a_scalar_hybrid_asm_opt.S
 */
#if defined(rax1_m1)
#undef rax1_m1
#endif

/* mlkem/fips202/native/aarch64/src/keccak_f1600_x4_v8a_scalar_hybrid_asm_opt.S
 */
#if defined(restore_gprs)
#undef restore_gprs
#endif

/* mlkem/fips202/native/aarch64/src/keccak_f1600_x4_v8a_scalar_hybrid_asm_opt.S
 */
#if defined(restore_vregs)
#undef restore_vregs
#endif

/* mlkem/fips202/native/aarch64/src/keccak_f1600_x4_v8a_scalar_hybrid_asm_opt.S
 */
#if defined(save_gprs)
#undef save_gprs
#endif

/* mlkem/fips202/native/aarch64/src/keccak_f1600_x4_v8a_scalar_hybrid_asm_opt.S
 */
#if defined(save_vregs)
#undef save_vregs
#endif

/* mlkem/fips202/native/aarch64/src/keccak_f1600_x4_v8a_scalar_hybrid_asm_opt.S
 */
#if defined(scalar_round_initial)
#undef scalar_round_initial
#endif

/* mlkem/fips202/native/aarch64/src/keccak_f1600_x4_v8a_scalar_hybrid_asm_opt.S
 */
#if defined(scalar_round_noninitial)
#undef scalar_round_noninitial
#endif

/* mlkem/fips202/native/aarch64/src/keccak_f1600_x4_v8a_scalar_hybrid_asm_opt.S
 */
#if defined(store_input_scalar)
#undef store_input_scalar
#endif

/* mlkem/fips202/native/aarch64/src/keccak_f1600_x4_v8a_scalar_hybrid_asm_opt.S
 */
#if defined(store_input_vector)
#undef store_input_vector
#endif

/* mlkem/fips202/native/aarch64/src/keccak_f1600_x4_v8a_scalar_hybrid_asm_opt.S
 */
#if defined(vector_round)
#undef vector_round
#endif

/* mlkem/fips202/native/aarch64/src/keccak_f1600_x4_v8a_scalar_hybrid_asm_opt.S
 */
#if defined(xar_m1)
#undef xar_m1
#endif

#include "mlkem/fips202/native/aarch64/src/keccak_f1600_x4_v8a_v84a_scalar_hybrid_asm_opt.S"

/*
 * Undo all #define directives from
 * mlkem/fips202/native/aarch64/src/keccak_f1600_x4_v8a_v84a_scalar_hybrid_asm_opt.S
 */

/* mlkem/fips202/native/aarch64/src/keccak_f1600_x4_v8a_v84a_scalar_hybrid_asm_opt.S
 */
#if defined(KECCAK_F1600_ROUNDS)
#undef KECCAK_F1600_ROUNDS
#endif

/* mlkem/fips202/native/aarch64/src/keccak_f1600_x4_v8a_v84a_scalar_hybrid_asm_opt.S
 */
#if defined(STACK_BASE_GPRS)
#undef STACK_BASE_GPRS
#endif

/* mlkem/fips202/native/aarch64/src/keccak_f1600_x4_v8a_v84a_scalar_hybrid_asm_opt.S
 */
#if defined(STACK_BASE_VREGS)
#undef STACK_BASE_VREGS
#endif

/* mlkem/fips202/native/aarch64/src/keccak_f1600_x4_v8a_v84a_scalar_hybrid_asm_opt.S
 */
#if defined(STACK_LOCS)
#undef STACK_LOCS
#endif

/* mlkem/fips202/native/aarch64/src/keccak_f1600_x4_v8a_v84a_scalar_hybrid_asm_opt.S
 */
#if defined(STACK_LOC_0)
#undef STACK_LOC_0
#endif

/* mlkem/fips202/native/aarch64/src/keccak_f1600_x4_v8a_v84a_scalar_hybrid_asm_opt.S
 */
#if defined(STACK_LOC_1)
#undef STACK_LOC_1
#endif

/* mlkem/fips202/native/aarch64/src/keccak_f1600_x4_v8a_v84a_scalar_hybrid_asm_opt.S
 */
#if defined(STACK_OFFSET_CONST_SCALAR)
#undef STACK_OFFSET_CONST_SCALAR
#endif

/* mlkem/fips202/native/aarch64/src/keccak_f1600_x4_v8a_v84a_scalar_hybrid_asm_opt.S
 */
#if defined(STACK_OFFSET_CONST_VECTOR)
#undef STACK_OFFSET_CONST_VECTOR
#endif

/* mlkem/fips202/native/aarch64/src/keccak_f1600_x4_v8a_v84a_scalar_hybrid_asm_opt.S
 */
#if defined(STACK_OFFSET_COUNT)
#undef STACK_OFFSET_COUNT
#endif

/* mlkem/fips202/native/aarch64/src/keccak_f1600_x4_v8a_v84a_scalar_hybrid_asm_opt.S
 */
#if defined(STACK_OFFSET_INPUT)
#undef STACK_OFFSET_INPUT
#endif

/* mlkem/fips202/native/aarch64/src/keccak_f1600_x4_v8a_v84a_scalar_hybrid_asm_opt.S
 */
#if defined(STACK_OFFSET_LOCS)
#undef STACK_OFFSET_LOCS
#endif

/* mlkem/fips202/native/aarch64/src/keccak_f1600_x4_v8a_v84a_scalar_hybrid_asm_opt.S
 */
#if defined(STACK_OFFSET_OUTER)
#undef STACK_OFFSET_OUTER
#endif

/* mlkem/fips202/native/aarch64/src/keccak_f1600_x4_v8a_v84a_scalar_hybrid_asm_opt.S
 */
#if defined(STACK_SIZE)
#undef STACK_SIZE
#endif

/* mlkem/fips202/native/aarch64/src/keccak_f1600_x4_v8a_v84a_scalar_hybrid_asm_opt.S
 */
#if defined(alloc_stack)
#undef alloc_stack
#endif

/* mlkem/fips202/native/aarch64/src/keccak_f1600_x4_v8a_v84a_scalar_hybrid_asm_opt.S
 */
#if defined(bcax_m0)
#undef bcax_m0
#endif

/* mlkem/fips202/native/aarch64/src/keccak_f1600_x4_v8a_v84a_scalar_hybrid_asm_opt.S
 */
#if defined(bcax_m1)
#undef bcax_m1
#endif

/* mlkem/fips202/native/aarch64/src/keccak_f1600_x4_v8a_v84a_scalar_hybrid_asm_opt.S
 */
#if defined(chi_step_ror)
#undef chi_step_ror
#endif

/* mlkem/fips202/native/aarch64/src/keccak_f1600_x4_v8a_v84a_scalar_hybrid_asm_opt.S
 */
#if defined(chi_step_ror2)
#undef chi_step_ror2
#endif

/* mlkem/fips202/native/aarch64/src/keccak_f1600_x4_v8a_v84a_scalar_hybrid_asm_opt.S
 */
#if defined(eor3_m0)
#undef eor3_m0
#endif

/* mlkem/fips202/native/aarch64/src/keccak_f1600_x4_v8a_v84a_scalar_hybrid_asm_opt.S
 */
#if defined(eor3_m1)
#undef eor3_m1
#endif

/* mlkem/fips202/native/aarch64/src/keccak_f1600_x4_v8a_v84a_scalar_hybrid_asm_opt.S
 */
#if defined(eor5)
#undef eor5
#endif

/* mlkem/fips202/native/aarch64/src/keccak_f1600_x4_v8a_v84a_scalar_hybrid_asm_opt.S
 */
#if defined(final_scalar_rotate)
#undef final_scalar_rotate
#endif

/* mlkem/fips202/native/aarch64/src/keccak_f1600_x4_v8a_v84a_scalar_hybrid_asm_opt.S
 */
#if defined(free_stack)
#undef free_stack
#endif

/* mlkem/fips202/native/aarch64/src/keccak_f1600_x4_v8a_v84a_scalar_hybrid_asm_opt.S
 */
#if defined(load_input_scalar)
#undef load_input_scalar
#endif

/* mlkem/fips202/native/aarch64/src/keccak_f1600_x4_v8a_v84a_scalar_hybrid_asm_opt.S
 */
#if defined(load_input_vector)
#undef load_input_vector
#endif

/* mlkem/fips202/native/aarch64/src/keccak_f1600_x4_v8a_v84a_scalar_hybrid_asm_opt.S
 */
#if defined(rax1_m0)
#undef rax1_m0
#endif

/* mlkem/fips202/native/aarch64/src/keccak_f1600_x4_v8a_v84a_scalar_hybrid_asm_opt.S
 */
#if defined(rax1_m1)
#undef rax1_m1
#endif

/* mlkem/fips202/native/aarch64/src/keccak_f1600_x4_v8a_v84a_scalar_hybrid_asm_opt.S
 */
#if defined(restore_gprs)
#undef restore_gprs
#endif

/* mlkem/fips202/native/aarch64/src/keccak_f1600_x4_v8a_v84a_scalar_hybrid_asm_opt.S
 */
#if defined(restore_vregs)
#undef restore_vregs
#endif

/* mlkem/fips202/native/aarch64/src/keccak_f1600_x4_v8a_v84a_scalar_hybrid_asm_opt.S
 */
#if defined(save_gprs)
#undef save_gprs
#endif

/* mlkem/fips202/native/aarch64/src/keccak_f1600_x4_v8a_v84a_scalar_hybrid_asm_opt.S
 */
#if defined(save_vregs)
#undef save_vregs
#endif

/* mlkem/fips202/native/aarch64/src/keccak_f1600_x4_v8a_v84a_scalar_hybrid_asm_opt.S
 */
#if defined(scalar_round_initial)
#undef scalar_round_initial
#endif

/* mlkem/fips202/native/aarch64/src/keccak_f1600_x4_v8a_v84a_scalar_hybrid_asm_opt.S
 */
#if defined(scalar_round_noninitial)
#undef scalar_round_noninitial
#endif

/* mlkem/fips202/native/aarch64/src/keccak_f1600_x4_v8a_v84a_scalar_hybrid_asm_opt.S
 */
#if defined(store_input_scalar)
#undef store_input_scalar
#endif

/* mlkem/fips202/native/aarch64/src/keccak_f1600_x4_v8a_v84a_scalar_hybrid_asm_opt.S
 */
#if defined(store_input_vector)
#undef store_input_vector
#endif

/* mlkem/fips202/native/aarch64/src/keccak_f1600_x4_v8a_v84a_scalar_hybrid_asm_opt.S
 */
#if defined(vector_round)
#undef vector_round
#endif

/* mlkem/fips202/native/aarch64/src/keccak_f1600_x4_v8a_v84a_scalar_hybrid_asm_opt.S
 */
#if defined(xar_m0)
#undef xar_m0
#endif

/* mlkem/fips202/native/aarch64/src/keccak_f1600_x4_v8a_v84a_scalar_hybrid_asm_opt.S
 */
#if defined(xar_m1)
#undef xar_m1
#endif

#endif /* MLKEM_NATIVE_MONOBUILD_NO_FIPS202_SOURCES */


/*
 * Undo all #define directives from mlkem/arith_backend.h
 */

/* mlkem/arith_backend.h */
#if defined(MLKEM_NATIVE_ARITH_IMPL_H)
#undef MLKEM_NATIVE_ARITH_IMPL_H
#endif


/*
 * Undo all #define directives from mlkem/cbd.h
 */

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


/*
 * Undo all #define directives from mlkem/cbmc.h
 */

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
#if defined(__contract__)
#undef __contract__
#endif

/* mlkem/cbmc.h */
#if defined(__loop__)
#undef __loop__
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


/*
 * Undo all #define directives from mlkem/common.h
 */

/* mlkem/common.h */
#if defined(FIPS202_ASM_NAMESPACE)
#undef FIPS202_ASM_NAMESPACE
#endif

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
#if defined(MLKEM_ASM_NAMESPACE)
#undef MLKEM_ASM_NAMESPACE
#endif

/* mlkem/common.h */
#if defined(MLKEM_NAMESPACE)
#undef MLKEM_NAMESPACE
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
#if defined(PREFIX_UNDERSCORE)
#undef PREFIX_UNDERSCORE
#endif

/* mlkem/common.h */
#if defined(PREFIX_UNDERSCORE_)
#undef PREFIX_UNDERSCORE_
#endif


/*
 * Undo all #define directives from mlkem/config.h
 */

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
#if defined(MLKEM_DEFAULT_NAMESPACE_PREFIX)
#undef MLKEM_DEFAULT_NAMESPACE_PREFIX
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


/*
 * Undo all #define directives from mlkem/debug/debug.h
 */

/* mlkem/debug/debug.h */
#if defined(BOUND)
#undef BOUND
#endif

/* mlkem/debug/debug.h */
#if defined(BOUND)
#undef BOUND
#endif

/* mlkem/debug/debug.h */
#if defined(CASSERT)
#undef CASSERT
#endif

/* mlkem/debug/debug.h */
#if defined(CASSERT)
#undef CASSERT
#endif

/* mlkem/debug/debug.h */
#if defined(MLKEM_DEBUG_H)
#undef MLKEM_DEBUG_H
#endif

/* mlkem/debug/debug.h */
#if defined(POLYVEC_BOUND)
#undef POLYVEC_BOUND
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
#if defined(POLYVEC_UBOUND)
#undef POLYVEC_UBOUND
#endif

/* mlkem/debug/debug.h */
#if defined(POLY_BOUND)
#undef POLY_BOUND
#endif

/* mlkem/debug/debug.h */
#if defined(POLY_BOUND)
#undef POLY_BOUND
#endif

/* mlkem/debug/debug.h */
#if defined(POLY_BOUND_MSG)
#undef POLY_BOUND_MSG
#endif

/* mlkem/debug/debug.h */
#if defined(POLY_BOUND_MSG)
#undef POLY_BOUND_MSG
#endif

/* mlkem/debug/debug.h */
#if defined(POLY_UBOUND)
#undef POLY_UBOUND
#endif

/* mlkem/debug/debug.h */
#if defined(POLY_UBOUND)
#undef POLY_UBOUND
#endif

/* mlkem/debug/debug.h */
#if defined(POLY_UBOUND_MSG)
#undef POLY_UBOUND_MSG
#endif

/* mlkem/debug/debug.h */
#if defined(POLY_UBOUND_MSG)
#undef POLY_UBOUND_MSG
#endif

/* mlkem/debug/debug.h */
#if defined(SCALAR_BOUND)
#undef SCALAR_BOUND
#endif

/* mlkem/debug/debug.h */
#if defined(SCALAR_BOUND)
#undef SCALAR_BOUND
#endif

/* mlkem/debug/debug.h */
#if defined(STATIC_ASSERT)
#undef STATIC_ASSERT
#endif

/* mlkem/debug/debug.h */
#if defined(UBOUND)
#undef UBOUND
#endif

/* mlkem/debug/debug.h */
#if defined(UBOUND)
#undef UBOUND
#endif

/* mlkem/debug/debug.h */
#if defined(mlkem_debug_assert)
#undef mlkem_debug_assert
#endif

/* mlkem/debug/debug.h */
#if defined(mlkem_debug_check_bounds)
#undef mlkem_debug_check_bounds
#endif


/*
 * Undo all #define directives from mlkem/indcpa.h
 */

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


/*
 * Undo all #define directives from mlkem/kem.h
 */

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


/*
 * Undo all #define directives from mlkem/mlkem_native.h
 */

/* mlkem/mlkem_native.h */
#if defined(BUILD_INFO_CONCAT)
#undef BUILD_INFO_CONCAT
#endif

/* mlkem/mlkem_native.h */
#if defined(BUILD_INFO_CONCAT_)
#undef BUILD_INFO_CONCAT_
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


/*
 * Undo all #define directives from mlkem/native/aarch64/clean.h
 */

/* mlkem/native/aarch64/clean.h */
#if defined(MLKEM_NATIVE_ARITH_BACKEND_AARCH64_CLEAN)
#undef MLKEM_NATIVE_ARITH_BACKEND_AARCH64_CLEAN
#endif

/* mlkem/native/aarch64/clean.h */
#if defined(MLKEM_NATIVE_ARITH_BACKEND_IMPL)
#undef MLKEM_NATIVE_ARITH_BACKEND_IMPL
#endif

/* mlkem/native/aarch64/clean.h */
#if defined(MLKEM_NATIVE_ARITH_BACKEND_NAME)
#undef MLKEM_NATIVE_ARITH_BACKEND_NAME
#endif

/* mlkem/native/aarch64/clean.h */
#if defined(MLKEM_NATIVE_ARITH_PROFILE_H)
#undef MLKEM_NATIVE_ARITH_PROFILE_H
#endif


/*
 * Undo all #define directives from mlkem/native/aarch64/opt.h
 */

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


/*
 * Undo all #define directives from
 * mlkem/native/aarch64/src/arith_native_aarch64.h
 */

/* mlkem/native/aarch64/src/arith_native_aarch64.h */
#if defined(MLKEM_AARCH64_NATIVE_H)
#undef MLKEM_AARCH64_NATIVE_H
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
#if defined(intt_asm_clean)
#undef intt_asm_clean
#endif

/* mlkem/native/aarch64/src/arith_native_aarch64.h */
#if defined(intt_asm_opt)
#undef intt_asm_opt
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
#if defined(poly_mulcache_compute_asm_clean)
#undef poly_mulcache_compute_asm_clean
#endif

/* mlkem/native/aarch64/src/arith_native_aarch64.h */
#if defined(poly_mulcache_compute_asm_opt)
#undef poly_mulcache_compute_asm_opt
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
#if defined(poly_tobytes_asm_clean)
#undef poly_tobytes_asm_clean
#endif

/* mlkem/native/aarch64/src/arith_native_aarch64.h */
#if defined(poly_tobytes_asm_opt)
#undef poly_tobytes_asm_opt
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
#if defined(polyvec_basemul_acc_montgomery_cached_asm_clean)
#undef polyvec_basemul_acc_montgomery_cached_asm_clean
#endif

/* mlkem/native/aarch64/src/arith_native_aarch64.h */
#if defined(polyvec_basemul_acc_montgomery_cached_asm_opt)
#undef polyvec_basemul_acc_montgomery_cached_asm_opt
#endif

/* mlkem/native/aarch64/src/arith_native_aarch64.h */
#if defined(rej_uniform_asm_clean)
#undef rej_uniform_asm_clean
#endif

/* mlkem/native/aarch64/src/arith_native_aarch64.h */
#if defined(rej_uniform_table)
#undef rej_uniform_table
#endif


/*
 * Undo all #define directives from mlkem/native/aarch64/src/clean_impl.h
 */

/* mlkem/native/aarch64/src/clean_impl.h */
#if defined(MLKEM_NATIVE_ARITH_PROFILE_IMPL_H)
#undef MLKEM_NATIVE_ARITH_PROFILE_IMPL_H
#endif

/* mlkem/native/aarch64/src/clean_impl.h */
#if defined(MLKEM_USE_NATIVE_INTT)
#undef MLKEM_USE_NATIVE_INTT
#endif

/* mlkem/native/aarch64/src/clean_impl.h */
#if defined(MLKEM_USE_NATIVE_NTT)
#undef MLKEM_USE_NATIVE_NTT
#endif

/* mlkem/native/aarch64/src/clean_impl.h */
#if defined(MLKEM_USE_NATIVE_POLYVEC_BASEMUL_ACC_MONTGOMERY_CACHED)
#undef MLKEM_USE_NATIVE_POLYVEC_BASEMUL_ACC_MONTGOMERY_CACHED
#endif

/* mlkem/native/aarch64/src/clean_impl.h */
#if defined(MLKEM_USE_NATIVE_POLY_MULCACHE_COMPUTE)
#undef MLKEM_USE_NATIVE_POLY_MULCACHE_COMPUTE
#endif

/* mlkem/native/aarch64/src/clean_impl.h */
#if defined(MLKEM_USE_NATIVE_POLY_REDUCE)
#undef MLKEM_USE_NATIVE_POLY_REDUCE
#endif

/* mlkem/native/aarch64/src/clean_impl.h */
#if defined(MLKEM_USE_NATIVE_POLY_TOBYTES)
#undef MLKEM_USE_NATIVE_POLY_TOBYTES
#endif

/* mlkem/native/aarch64/src/clean_impl.h */
#if defined(MLKEM_USE_NATIVE_POLY_TOMONT)
#undef MLKEM_USE_NATIVE_POLY_TOMONT
#endif

/* mlkem/native/aarch64/src/clean_impl.h */
#if defined(MLKEM_USE_NATIVE_REJ_UNIFORM)
#undef MLKEM_USE_NATIVE_REJ_UNIFORM
#endif


/*
 * Undo all #define directives from mlkem/native/aarch64/src/consts.h
 */

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


/*
 * Undo all #define directives from mlkem/native/aarch64/src/opt_impl.h
 */

/* mlkem/native/aarch64/src/opt_impl.h */
#if defined(MLKEM_NATIVE_ARITH_PROFILE_IMPL_H)
#undef MLKEM_NATIVE_ARITH_PROFILE_IMPL_H
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


/*
 * Undo all #define directives from mlkem/native/api.h
 */

/* mlkem/native/api.h */
#if defined(MLKEM_NATIVE_ARITH_NATIVE_API_H)
#undef MLKEM_NATIVE_ARITH_NATIVE_API_H
#endif


/*
 * Undo all #define directives from mlkem/native/default.h
 */

/* mlkem/native/default.h */
#if defined(MLKEM_NATIVE_ARITH_BACKEND_DEFAULT_H)
#undef MLKEM_NATIVE_ARITH_BACKEND_DEFAULT_H
#endif


/*
 * Undo all #define directives from mlkem/native/x86_64/default.h
 */

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


/*
 * Undo all #define directives from mlkem/native/x86_64/src/align.h
 */

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


/*
 * Undo all #define directives from
 * mlkem/native/x86_64/src/arith_native_x86_64.h
 */

/* mlkem/native/x86_64/src/arith_native_x86_64.h */
#if defined(MLKEM_X86_64_NATIVE_H)
#undef MLKEM_X86_64_NATIVE_H
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


/*
 * Undo all #define directives from mlkem/native/x86_64/src/consts.h
 */

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
#if defined(qdata)
#undef qdata
#endif


/*
 * Undo all #define directives from mlkem/native/x86_64/src/default_impl.h
 */

/* mlkem/native/x86_64/src/default_impl.h */
#if defined(MLKEM_NATIVE_ARITH_PROFILE_IMPL_H)
#undef MLKEM_NATIVE_ARITH_PROFILE_IMPL_H
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


/*
 * Undo all #define directives from mlkem/ntt.h
 */

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


/*
 * Undo all #define directives from mlkem/params.h
 */

/* mlkem/params.h */
#if defined(KECCAK_WAY)
#undef KECCAK_WAY
#endif

/* mlkem/params.h */
#if defined(MLKEM_ETA1)
#undef MLKEM_ETA1
#endif

/* mlkem/params.h */
#if defined(MLKEM_ETA1)
#undef MLKEM_ETA1
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
#if defined(MLKEM_LVL)
#undef MLKEM_LVL
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
#if defined(MLKEM_POLYCOMPRESSEDBYTES_DU)
#undef MLKEM_POLYCOMPRESSEDBYTES_DU
#endif

/* mlkem/params.h */
#if defined(MLKEM_POLYCOMPRESSEDBYTES_DU)
#undef MLKEM_POLYCOMPRESSEDBYTES_DU
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
#if defined(MLKEM_POLYCOMPRESSEDBYTES_DV)
#undef MLKEM_POLYCOMPRESSEDBYTES_DV
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
#if defined(MLKEM_POLYVECCOMPRESSEDBYTES_DU)
#undef MLKEM_POLYVECCOMPRESSEDBYTES_DU
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


/*
 * Undo all #define directives from mlkem/poly.h
 */

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
#if defined(poly_compress_du)
#undef poly_compress_du
#endif

/* mlkem/poly.h */
#if defined(poly_compress_dv)
#undef poly_compress_dv
#endif

/* mlkem/poly.h */
#if defined(poly_decompress_du)
#undef poly_decompress_du
#endif

/* mlkem/poly.h */
#if defined(poly_decompress_dv)
#undef poly_decompress_dv
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
#if defined(poly_getnoise_eta1122_4x)
#undef poly_getnoise_eta1122_4x
#endif

/* mlkem/poly.h */
#if defined(poly_getnoise_eta1_4x)
#undef poly_getnoise_eta1_4x
#endif

/* mlkem/poly.h */
#if defined(poly_getnoise_eta2)
#undef poly_getnoise_eta2
#endif

/* mlkem/poly.h */
#if defined(poly_getnoise_eta2_4x)
#undef poly_getnoise_eta2_4x
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


/*
 * Undo all #define directives from mlkem/polyvec.h
 */

/* mlkem/polyvec.h */
#if defined(POLYVEC_H)
#undef POLYVEC_H
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


/*
 * Undo all #define directives from mlkem/reduce.h
 */

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


/*
 * Undo all #define directives from mlkem/rej_uniform.h
 */

/* mlkem/rej_uniform.h */
#if defined(REJ_UNIFORM_H)
#undef REJ_UNIFORM_H
#endif

/* mlkem/rej_uniform.h */
#if defined(rej_uniform)
#undef rej_uniform
#endif


/*
 * Undo all #define directives from mlkem/symmetric.h
 */

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


/*
 * Undo all #define directives from mlkem/sys.h
 */

/* mlkem/sys.h */
#if defined(ALIGN)
#undef ALIGN
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
#if defined(ALWAYS_INLINE)
#undef ALWAYS_INLINE
#endif

/* mlkem/sys.h */
#if defined(ALWAYS_INLINE)
#undef ALWAYS_INLINE
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
#if defined(INLINE)
#undef INLINE
#endif

/* mlkem/sys.h */
#if defined(INLINE)
#undef INLINE
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
#if defined(RESTRICT)
#undef RESTRICT
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

/* mlkem/sys.h */
#if defined(asm)
#undef asm
#endif


/*
 * Undo all #define directives from mlkem/verify.h
 */

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


#if !defined(MLKEM_NATIVE_MONOBUILD_KEEP_SHARED_HEADERS)

/*
 * Undo all #define directives from mlkem/fips202/fips202.h
 */

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


/*
 * Undo all #define directives from mlkem/fips202/fips202_backend.h
 */

/* mlkem/fips202/fips202_backend.h */
#if defined(MLKEM_NATIVE_FIPS202_IMPL_H)
#undef MLKEM_NATIVE_FIPS202_IMPL_H
#endif


/*
 * Undo all #define directives from mlkem/fips202/fips202x4.h
 */

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


/*
 * Undo all #define directives from mlkem/fips202/keccakf1600.h
 */

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


/*
 * Undo all #define directives from mlkem/fips202/native/aarch64/cortex_a55.h
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


/*
 * Undo all #define directives from mlkem/fips202/native/aarch64/default.h
 */

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


/*
 * Undo all #define directives from
 * mlkem/fips202/native/aarch64/src/cortex_a55_impl.h
 */

/* mlkem/fips202/native/aarch64/src/cortex_a55_impl.h */
#if defined(FIPS202_NATIVE_PROFILE_IMPL_H)
#undef FIPS202_NATIVE_PROFILE_IMPL_H
#endif

/* mlkem/fips202/native/aarch64/src/cortex_a55_impl.h */
#if defined(MLKEM_USE_FIPS202_X1_NATIVE)
#undef MLKEM_USE_FIPS202_X1_NATIVE
#endif


/*
 * Undo all #define directives from
 * mlkem/fips202/native/aarch64/src/default_impl.h
 */

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


/*
 * Undo all #define directives from
 * mlkem/fips202/native/aarch64/src/fips202_native_aarch64.h
 */

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


/*
 * Undo all #define directives from mlkem/fips202/native/api.h
 */

/* mlkem/fips202/native/api.h */
#if defined(MLKEM_NATIVE_FIPS202_NATIVE_API_H)
#undef MLKEM_NATIVE_FIPS202_NATIVE_API_H
#endif


/*
 * Undo all #define directives from mlkem/fips202/native/default.h
 */

/* mlkem/fips202/native/default.h */
#if defined(MLKEM_NATIVE_FIPS202_BACKEND_DEFAULT_H)
#undef MLKEM_NATIVE_FIPS202_BACKEND_DEFAULT_H
#endif


/*
 * Undo all #define directives from mlkem/fips202/native/x86_64/src/xkcp_impl.h
 */

/* mlkem/fips202/native/x86_64/src/xkcp_impl.h */
#if defined(KeccakP1600times4_PermuteAll_24rounds)
#undef KeccakP1600times4_PermuteAll_24rounds
#endif

/* mlkem/fips202/native/x86_64/src/xkcp_impl.h */
#if defined(MLKEM_NATIVE_FIPS202_PROFILE_IMPL_H)
#undef MLKEM_NATIVE_FIPS202_PROFILE_IMPL_H
#endif

/* mlkem/fips202/native/x86_64/src/xkcp_impl.h */
#if defined(MLKEM_USE_FIPS202_X4_NATIVE)
#undef MLKEM_USE_FIPS202_X4_NATIVE
#endif


/*
 * Undo all #define directives from mlkem/fips202/native/x86_64/xkcp.h
 */

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
#if defined(MLKEM_NATIVE_FIPS202_PROFILE_H)
#undef MLKEM_NATIVE_FIPS202_PROFILE_H
#endif


/*
 * Undo all #define directives from mlkem/randombytes.h
 */

/* mlkem/randombytes.h */
#if defined(RANDOMBYTES_H)
#undef RANDOMBYTES_H
#endif

#endif /* MLKEM_NATIVE_MONOBUILD_KEEP_SHARED_HEADERS */
