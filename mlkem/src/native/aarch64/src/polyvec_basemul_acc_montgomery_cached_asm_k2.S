/*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */

/* References
 * ==========
 *
 * - [NeonNTT]
 *   Neon NTT: Faster Dilithium, Kyber, and Saber on Cortex-A72 and Apple M1
 *   Becker, Hwang, Kannwischer, Yang, Yang
 *   https://eprint.iacr.org/2021/986
 */

/* Re-implementation of asymmetric base multiplication following @[NeonNTT] */

#include "../../../common.h"
#if defined(MLK_ARITH_BACKEND_AARCH64) &&  !defined(MLK_CONFIG_MULTILEVEL_NO_SHARED) &&  (defined(MLK_CONFIG_MULTILEVEL_WITH_SHARED) || MLKEM_K == 2)

/*
 * WARNING: This file is auto-derived from the mlkem-native source file
 *   dev/aarch64_opt/src/polyvec_basemul_acc_montgomery_cached_asm_k2.S using scripts/simpasm. Do not modify it directly.
 */


.text
.balign 4
.global MLK_ASM_NAMESPACE(polyvec_basemul_acc_montgomery_cached_asm_k2)
MLK_ASM_FN_SYMBOL(polyvec_basemul_acc_montgomery_cached_asm_k2)

        sub	sp, sp, #0x40
        stp	d8, d9, [sp]
        stp	d10, d11, [sp, #0x10]
        stp	d12, d13, [sp, #0x20]
        stp	d14, d15, [sp, #0x30]
        mov	w14, #0xd01             // =3329
        dup	v0.8h, w14
        mov	w14, #0xcff             // =3327
        dup	v2.8h, w14
        add	x4, x1, #0x200
        add	x5, x2, #0x200
        add	x6, x3, #0x100
        mov	x13, #0x10              // =16
        ldr	q25, [x1, #0x10]
        ldr	q6, [x1], #0x20
        ldr	q12, [x2], #0x20
        ldur	q20, [x2, #-0x10]
        ldr	q7, [x4], #0x20
        ldur	q10, [x4, #-0x10]
        ldr	q14, [x5], #0x20
        ldur	q29, [x5, #-0x10]
        uzp1	v24.8h, v6.8h, v25.8h
        ld1	{ v16.8h }, [x3], #16
        uzp2	v30.8h, v12.8h, v20.8h
        uzp1	v12.8h, v12.8h, v20.8h
        ld1	{ v20.8h }, [x6], #16
        uzp2	v18.8h, v6.8h, v25.8h
        uzp1	v22.8h, v14.8h, v29.8h
        smull2	v8.4s, v24.8h, v12.8h
        uzp1	v4.8h, v7.8h, v10.8h
        smull	v15.4s, v24.4h, v12.4h
        smlal	v15.4s, v18.4h, v16.4h
        ldr	q13, [x1, #0x10]
        smull	v25.4s, v24.4h, v30.4h
        uzp2	v27.8h, v14.8h, v29.8h
        smull2	v11.4s, v24.8h, v30.8h
        uzp2	v1.8h, v7.8h, v10.8h
        smlal2	v8.4s, v18.8h, v16.8h
        smlal2	v11.4s, v18.8h, v12.8h
        ldr	q7, [x1], #0x20
        smlal2	v8.4s, v4.8h, v22.8h
        ldr	q14, [x2], #0x20
        smlal	v15.4s, v4.4h, v22.4h
        ldur	q24, [x2, #-0x10]
        smlal2	v8.4s, v1.8h, v20.8h
        ldr	q9, [x4, #0x10]
        smlal2	v11.4s, v4.8h, v27.8h
        uzp1	v5.8h, v7.8h, v13.8h
        smlal	v15.4s, v1.4h, v20.4h
        ldr	q21, [x5], #0x20
        smlal	v25.4s, v18.4h, v12.4h
        uzp2	v20.8h, v7.8h, v13.8h
        smlal	v25.4s, v4.4h, v27.4h
        ld1	{ v31.8h }, [x3], #16
        smlal	v25.4s, v1.4h, v22.4h
        uzp1	v28.8h, v14.8h, v24.8h
        smlal2	v11.4s, v1.8h, v22.8h
        uzp1	v12.8h, v15.8h, v8.8h
        ldr	q6, [x4], #0x20
        smull	v26.4s, v5.4h, v28.4h
        mul	v18.8h, v12.8h, v2.8h
        ldur	q17, [x5, #-0x10]
        uzp1	v1.8h, v25.8h, v11.8h
        smull2	v23.4s, v5.8h, v28.8h
        smlal2	v23.4s, v20.8h, v31.8h
        mul	v10.8h, v1.8h, v2.8h
        uzp1	v30.8h, v21.8h, v17.8h
        uzp1	v16.8h, v6.8h, v9.8h
        smlal	v15.4s, v18.4h, v0.4h
        ld1	{ v3.8h }, [x6], #16
        smlal2	v23.4s, v16.8h, v30.8h
        smlal2	v8.4s, v18.8h, v0.8h
        smlal	v25.4s, v10.4h, v0.4h
        uzp2	v12.8h, v6.8h, v9.8h
        smlal	v26.4s, v20.4h, v31.4h
        smlal2	v11.4s, v10.8h, v0.8h
        smlal2	v23.4s, v12.8h, v3.8h
        uzp2	v13.8h, v15.8h, v8.8h
        uzp2	v29.8h, v14.8h, v24.8h
        smlal	v26.4s, v16.4h, v30.4h
        uzp2	v17.8h, v21.8h, v17.8h
        smlal	v26.4s, v12.4h, v3.4h
        uzp2	v19.8h, v25.8h, v11.8h
        smull	v18.4s, v5.4h, v29.4h
        smlal	v18.4s, v20.4h, v28.4h
        smlal	v18.4s, v16.4h, v17.4h
        zip2	v10.8h, v13.8h, v19.8h
        uzp1	v3.8h, v26.8h, v23.8h
        smlal	v18.4s, v12.4h, v30.4h
        smull2	v8.4s, v5.8h, v29.8h
        str	q10, [x0, #0x10]
        zip1	v25.8h, v13.8h, v19.8h
        mul	v15.8h, v3.8h, v2.8h
        sub	x13, x13, #0x2

polyvec_basemul_acc_montgomery_cached_k2_loop_start:
        ldr	q22, [x1, #0x10]
        ldr	q11, [x1], #0x20
        ldr	q14, [x2], #0x20
        smlal2	v8.4s, v20.8h, v28.8h
        ldur	q4, [x2, #-0x10]
        smlal2	v8.4s, v16.8h, v17.8h
        ldr	q24, [x4, #0x10]
        smlal2	v8.4s, v12.8h, v30.8h
        uzp1	v19.8h, v11.8h, v22.8h
        ldr	q7, [x4], #0x20
        ldr	q13, [x5], #0x20
        ldur	q17, [x5, #-0x10]
        uzp2	v20.8h, v11.8h, v22.8h
        smlal	v26.4s, v15.4h, v0.4h
        smlal2	v23.4s, v15.8h, v0.8h
        uzp1	v5.8h, v18.8h, v8.8h
        ld1	{ v27.8h }, [x3], #16
        uzp1	v28.8h, v14.8h, v4.8h
        mul	v11.8h, v5.8h, v2.8h
        uzp1	v30.8h, v13.8h, v17.8h
        uzp1	v16.8h, v7.8h, v24.8h
        ld1	{ v15.8h }, [x6], #16
        uzp2	v22.8h, v26.8h, v23.8h
        smull2	v23.4s, v19.8h, v28.8h
        smlal2	v23.4s, v20.8h, v27.8h
        uzp2	v17.8h, v13.8h, v17.8h
        uzp2	v12.8h, v7.8h, v24.8h
        smlal2	v23.4s, v16.8h, v30.8h
        uzp2	v31.8h, v14.8h, v4.8h
        smlal	v18.4s, v11.4h, v0.4h
        smull	v26.4s, v19.4h, v28.4h
        smlal	v26.4s, v20.4h, v27.4h
        smlal2	v8.4s, v11.8h, v0.8h
        smlal2	v23.4s, v12.8h, v15.8h
        smlal	v26.4s, v16.4h, v30.4h
        smlal	v26.4s, v12.4h, v15.4h
        str	q25, [x0], #0x20
        uzp2	v9.8h, v18.8h, v8.8h
        smull	v18.4s, v19.4h, v31.4h
        smlal	v18.4s, v20.4h, v28.4h
        smlal	v18.4s, v16.4h, v17.4h
        zip2	v3.8h, v22.8h, v9.8h
        uzp1	v29.8h, v26.8h, v23.8h
        smlal	v18.4s, v12.4h, v30.4h
        smull2	v8.4s, v19.8h, v31.8h
        str	q3, [x0, #0x10]
        zip1	v25.8h, v22.8h, v9.8h
        mul	v15.8h, v29.8h, v2.8h
        subs	x13, x13, #0x1
        cbnz	x13, polyvec_basemul_acc_montgomery_cached_k2_loop_start
        str	q25, [x0], #0x20
        smlal2	v8.4s, v20.8h, v28.8h
        smlal2	v8.4s, v16.8h, v17.8h
        smlal2	v8.4s, v12.8h, v30.8h
        smlal2	v23.4s, v15.8h, v0.8h
        smlal	v26.4s, v15.4h, v0.4h
        uzp1	v12.8h, v18.8h, v8.8h
        uzp2	v15.8h, v26.8h, v23.8h
        mul	v12.8h, v12.8h, v2.8h
        smlal	v18.4s, v12.4h, v0.4h
        smlal2	v8.4s, v12.8h, v0.8h
        uzp2	v30.8h, v18.8h, v8.8h
        zip1	v12.8h, v15.8h, v30.8h
        zip2	v19.8h, v15.8h, v30.8h
        str	q12, [x0], #0x20
        stur	q19, [x0, #-0x10]
        ldp	d8, d9, [sp]
        ldp	d10, d11, [sp, #0x10]
        ldp	d12, d13, [sp, #0x20]
        ldp	d14, d15, [sp, #0x30]
        add	sp, sp, #0x40
        ret


#endif /* MLK_ARITH_BACKEND_AARCH64 && !MLK_CONFIG_MULTILEVEL_NO_SHARED && \
          (MLK_CONFIG_MULTILEVEL_WITH_SHARED || MLKEM_K == 2) */
