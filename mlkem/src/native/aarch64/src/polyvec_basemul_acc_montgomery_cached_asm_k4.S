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
#if defined(MLK_ARITH_BACKEND_AARCH64) &&  !defined(MLK_CONFIG_MULTILEVEL_NO_SHARED) &&  (defined(MLK_CONFIG_MULTILEVEL_WITH_SHARED) || MLKEM_K == 4)

/*
 * WARNING: This file is auto-derived from the mlkem-native source file
 *   dev/aarch64_opt/src/polyvec_basemul_acc_montgomery_cached_asm_k4.S using scripts/simpasm. Do not modify it directly.
 */


.text
.balign 4
.global MLK_ASM_NAMESPACE(polyvec_basemul_acc_montgomery_cached_asm_k4)
MLK_ASM_FN_SYMBOL(polyvec_basemul_acc_montgomery_cached_asm_k4)

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
        add	x7, x1, #0x400
        add	x8, x2, #0x400
        add	x9, x3, #0x200
        add	x10, x1, #0x600
        add	x11, x2, #0x600
        add	x12, x3, #0x300
        mov	x13, #0x10              // =16
        ldr	q10, [x1, #0x10]
        ldr	q26, [x1], #0x20
        ldr	q13, [x2, #0x10]
        ldr	q11, [x4], #0x20
        ldr	q12, [x2], #0x20
        ld1	{ v6.8h }, [x6], #16
        ldur	q3, [x4, #-0x10]
        ldr	q31, [x8], #0x20
        ld1	{ v21.8h }, [x3], #16
        uzp2	v1.8h, v26.8h, v10.8h
        uzp1	v25.8h, v26.8h, v10.8h
        ldr	q30, [x5], #0x20
        ldur	q27, [x5, #-0x10]
        uzp1	v5.8h, v12.8h, v13.8h
        uzp1	v9.8h, v11.8h, v3.8h
        ldr	q20, [x7, #0x10]
        ldr	q10, [x7], #0x20
        smull2	v17.4s, v25.8h, v5.8h
        ldur	q29, [x8, #-0x10]
        smull	v14.4s, v25.4h, v5.4h
        uzp1	v28.8h, v30.8h, v27.8h
        smlal	v14.4s, v1.4h, v21.4h
        smlal2	v17.4s, v1.8h, v21.8h
        uzp2	v24.8h, v11.8h, v3.8h
        smlal	v14.4s, v9.4h, v28.4h
        uzp1	v18.8h, v10.8h, v20.8h
        uzp1	v26.8h, v31.8h, v29.8h
        smlal2	v17.4s, v9.8h, v28.8h
        smlal2	v17.4s, v24.8h, v6.8h
        uzp2	v20.8h, v10.8h, v20.8h
        smlal	v14.4s, v24.4h, v6.4h
        uzp2	v13.8h, v12.8h, v13.8h
        ldr	q19, [x11], #0x20
        smlal	v14.4s, v18.4h, v26.4h
        ld1	{ v7.8h }, [x9], #16
        smull	v11.4s, v25.4h, v13.4h
        ldr	q3, [x10, #0x10]
        smull2	v15.4s, v25.8h, v13.8h
        smlal	v11.4s, v1.4h, v5.4h
        ldur	q21, [x11, #-0x10]
        ldr	q12, [x10], #0x20
        smlal2	v15.4s, v1.8h, v5.8h
        uzp2	v4.8h, v30.8h, v27.8h
        smlal2	v17.4s, v18.8h, v26.8h
        uzp2	v30.8h, v31.8h, v29.8h
        smlal	v14.4s, v20.4h, v7.4h
        smlal	v11.4s, v9.4h, v4.4h
        uzp1	v23.8h, v19.8h, v21.8h
        ld1	{ v13.8h }, [x12], #16
        smlal	v11.4s, v24.4h, v28.4h
        smlal2	v15.4s, v9.8h, v4.8h
        uzp1	v25.8h, v12.8h, v3.8h
        smlal	v11.4s, v18.4h, v30.4h
        uzp2	v12.8h, v12.8h, v3.8h
        ldr	q16, [x2], #0x20
        smlal	v14.4s, v25.4h, v23.4h
        ldr	q10, [x1, #0x10]
        smlal	v14.4s, v12.4h, v13.4h
        ldur	q3, [x2, #-0x10]
        smlal2	v17.4s, v20.8h, v7.8h
        smlal2	v17.4s, v25.8h, v23.8h
        ldr	q1, [x1], #0x20
        smlal2	v17.4s, v12.8h, v13.8h
        uzp2	v21.8h, v19.8h, v21.8h
        ldr	q22, [x8], #0x20
        smlal	v11.4s, v20.4h, v26.4h
        smlal	v11.4s, v25.4h, v21.4h
        uzp2	v27.8h, v16.8h, v3.8h
        smlal	v11.4s, v12.4h, v23.4h
        ldr	q13, [x4], #0x20
        smlal2	v15.4s, v24.8h, v28.8h
        uzp1	v31.8h, v14.8h, v17.8h
        smlal2	v15.4s, v18.8h, v30.8h
        uzp1	v16.8h, v16.8h, v3.8h
        uzp1	v19.8h, v1.8h, v10.8h
        mul	v7.8h, v31.8h, v2.8h
        uzp2	v4.8h, v1.8h, v10.8h
        ldur	q31, [x4, #-0x10]
        ldr	q29, [x5], #0x20
        smull2	v8.4s, v19.8h, v27.8h
        ld1	{ v5.8h }, [x3], #16
        smlal2	v8.4s, v4.8h, v16.8h
        ld1	{ v9.8h }, [x12], #16
        smlal2	v15.4s, v20.8h, v26.8h
        ldur	q24, [x5, #-0x10]
        smlal	v14.4s, v7.4h, v0.4h
        uzp1	v1.8h, v13.8h, v31.8h
        smlal2	v17.4s, v7.8h, v0.8h
        ld1	{ v30.8h }, [x6], #16
        smlal2	v15.4s, v25.8h, v21.8h
        ldr	q6, [x7, #0x10]
        smlal2	v15.4s, v12.8h, v23.8h
        ldr	q7, [x7], #0x20
        smull	v18.4s, v19.4h, v27.4h
        ldur	q21, [x8, #-0x10]
        smull	v26.4s, v19.4h, v16.4h
        smull2	v23.4s, v19.8h, v16.8h
        uzp1	v10.8h, v29.8h, v24.8h
        uzp1	v28.8h, v11.8h, v15.8h
        smlal	v26.4s, v4.4h, v5.4h
        uzp2	v19.8h, v14.8h, v17.8h
        smlal	v26.4s, v1.4h, v10.4h
        uzp2	v25.8h, v13.8h, v31.8h
        mul	v13.8h, v28.8h, v2.8h
        uzp1	v31.8h, v7.8h, v6.8h
        ldr	q20, [x10, #0x10]
        smlal2	v23.4s, v4.8h, v5.8h
        uzp1	v28.8h, v22.8h, v21.8h
        ldr	q12, [x11, #0x10]
        smlal	v26.4s, v25.4h, v30.4h
        ldr	q14, [x11], #0x20
        smlal	v26.4s, v31.4h, v28.4h
        ld1	{ v3.8h }, [x9], #16
        smlal	v11.4s, v13.4h, v0.4h
        ldr	q5, [x10], #0x20
        smlal2	v15.4s, v13.8h, v0.8h
        uzp2	v7.8h, v7.8h, v6.8h
        smlal2	v23.4s, v1.8h, v10.8h
        uzp1	v13.8h, v14.8h, v12.8h
        smlal2	v23.4s, v25.8h, v30.8h
        smlal	v26.4s, v7.4h, v3.4h
        uzp2	v17.8h, v22.8h, v21.8h
        smlal2	v23.4s, v31.8h, v28.8h
        uzp2	v30.8h, v29.8h, v24.8h
        uzp2	v29.8h, v5.8h, v20.8h
        smlal	v18.4s, v4.4h, v16.4h
        uzp1	v21.8h, v5.8h, v20.8h
        smlal	v18.4s, v1.4h, v30.4h
        smlal2	v23.4s, v7.8h, v3.8h
        uzp2	v27.8h, v11.8h, v15.8h
        uzp2	v15.8h, v14.8h, v12.8h
        smlal	v26.4s, v21.4h, v13.4h
        zip2	v6.8h, v19.8h, v27.8h
        smlal	v18.4s, v25.4h, v10.4h
        zip1	v16.8h, v19.8h, v27.8h
        smlal	v26.4s, v29.4h, v9.4h
        sub	x13, x13, #0x2

polyvec_basemul_acc_montgomery_cached_k4_loop_start:
        smlal2	v23.4s, v21.8h, v13.8h
        ldr	q11, [x1], #0x20
        smlal2	v23.4s, v29.8h, v9.8h
        ldr	q24, [x4], #0x20
        smlal	v18.4s, v31.4h, v17.4h
        ldur	q22, [x1, #-0x10]
        ldr	q27, [x7, #0x10]
        smlal	v18.4s, v7.4h, v28.4h
        ldr	q14, [x2], #0x20
        smlal	v18.4s, v21.4h, v15.4h
        smlal	v18.4s, v29.4h, v13.4h
        uzp1	v4.8h, v26.8h, v23.8h
        smlal2	v8.4s, v1.8h, v30.8h
        uzp1	v19.8h, v11.8h, v22.8h
        mul	v4.8h, v4.8h, v2.8h
        uzp2	v5.8h, v11.8h, v22.8h
        ldur	q11, [x4, #-0x10]
        ldr	q3, [x5], #0x20
        smlal2	v8.4s, v25.8h, v10.8h
        ld1	{ v22.8h }, [x3], #16
        ldur	q30, [x2, #-0x10]
        smlal2	v8.4s, v31.8h, v17.8h
        smlal2	v8.4s, v7.8h, v28.8h
        ldur	q17, [x5, #-0x10]
        smlal	v26.4s, v4.4h, v0.4h
        uzp1	v1.8h, v24.8h, v11.8h
        smlal2	v23.4s, v4.8h, v0.8h
        ld1	{ v20.8h }, [x6], #16
        smlal2	v8.4s, v21.8h, v15.8h
        uzp1	v12.8h, v14.8h, v30.8h
        smlal2	v8.4s, v29.8h, v13.8h
        ldr	q13, [x7], #0x20
        ldr	q9, [x8], #0x20
        ldur	q21, [x8, #-0x10]
        uzp2	v4.8h, v26.8h, v23.8h
        smull	v26.4s, v19.4h, v12.4h
        smull2	v23.4s, v19.8h, v12.8h
        uzp1	v10.8h, v3.8h, v17.8h
        uzp1	v7.8h, v18.8h, v8.8h
        smlal	v26.4s, v5.4h, v22.4h
        uzp2	v25.8h, v24.8h, v11.8h
        smlal	v26.4s, v1.4h, v10.4h
        uzp1	v31.8h, v13.8h, v27.8h
        mul	v29.8h, v7.8h, v2.8h
        ldr	q24, [x10, #0x10]
        uzp2	v14.8h, v14.8h, v30.8h
        smlal2	v23.4s, v5.8h, v22.8h
        uzp1	v28.8h, v9.8h, v21.8h
        smlal	v26.4s, v25.4h, v20.4h
        uzp2	v30.8h, v3.8h, v17.8h
        ldr	q15, [x10], #0x20
        smlal	v26.4s, v31.4h, v28.4h
        ld1	{ v3.8h }, [x9], #16
        smlal	v18.4s, v29.4h, v0.4h
        uzp2	v7.8h, v13.8h, v27.8h
        smlal2	v8.4s, v29.8h, v0.8h
        ldr	q27, [x11], #0x20
        smlal2	v23.4s, v1.8h, v10.8h
        uzp2	v17.8h, v9.8h, v21.8h
        smlal2	v23.4s, v25.8h, v20.8h
        smlal	v26.4s, v7.4h, v3.4h
        ldur	q20, [x11, #-0x10]
        uzp2	v11.8h, v18.8h, v8.8h
        smull2	v8.4s, v19.8h, v14.8h
        str	q16, [x0], #0x20
        smull	v18.4s, v19.4h, v14.4h
        uzp1	v21.8h, v15.8h, v24.8h
        smlal	v18.4s, v5.4h, v12.4h
        smlal2	v8.4s, v5.8h, v12.8h
        uzp1	v13.8h, v27.8h, v20.8h
        smlal	v18.4s, v1.4h, v30.4h
        ld1	{ v9.8h }, [x12], #16
        smlal2	v23.4s, v31.8h, v28.8h
        uzp2	v29.8h, v15.8h, v24.8h
        uzp2	v15.8h, v27.8h, v20.8h
        smlal	v26.4s, v21.4h, v13.4h
        smlal	v18.4s, v25.4h, v10.4h
        stur	q6, [x0, #-0x10]
        zip1	v16.8h, v4.8h, v11.8h
        smlal	v26.4s, v29.4h, v9.4h
        smlal2	v23.4s, v7.8h, v3.8h
        zip2	v6.8h, v4.8h, v11.8h
        subs	x13, x13, #0x1
        cbnz	x13, polyvec_basemul_acc_montgomery_cached_k4_loop_start
        str	q6, [x0, #0x10]
        smlal2	v23.4s, v21.8h, v13.8h
        smlal2	v8.4s, v1.8h, v30.8h
        str	q16, [x0], #0x20
        smlal2	v8.4s, v25.8h, v10.8h
        smlal	v18.4s, v31.4h, v17.4h
        smlal2	v23.4s, v29.8h, v9.8h
        smlal2	v8.4s, v31.8h, v17.8h
        smlal2	v8.4s, v7.8h, v28.8h
        smlal	v18.4s, v7.4h, v28.4h
        smlal	v18.4s, v21.4h, v15.4h
        smlal2	v8.4s, v21.8h, v15.8h
        smlal	v18.4s, v29.4h, v13.4h
        smlal2	v8.4s, v29.8h, v13.8h
        uzp1	v13.8h, v26.8h, v23.8h
        mul	v13.8h, v13.8h, v2.8h
        uzp1	v10.8h, v18.8h, v8.8h
        mul	v10.8h, v10.8h, v2.8h
        smlal	v26.4s, v13.4h, v0.4h
        smlal2	v23.4s, v13.8h, v0.8h
        smlal	v18.4s, v10.4h, v0.4h
        smlal2	v8.4s, v10.8h, v0.8h
        uzp2	v21.8h, v26.8h, v23.8h
        uzp2	v13.8h, v18.8h, v8.8h
        zip2	v20.8h, v21.8h, v13.8h
        zip1	v13.8h, v21.8h, v13.8h
        str	q13, [x0], #0x20
        stur	q20, [x0, #-0x10]
        ldp	d8, d9, [sp]
        ldp	d10, d11, [sp, #0x10]
        ldp	d12, d13, [sp, #0x20]
        ldp	d14, d15, [sp, #0x30]
        add	sp, sp, #0x40
        ret

#endif /* MLK_ARITH_BACKEND_AARCH64 && !MLK_CONFIG_MULTILEVEL_NO_SHARED && \
          (MLK_CONFIG_MULTILEVEL_WITH_SHARED || MLKEM_K == 4) */
