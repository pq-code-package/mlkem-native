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


/*
 * WARNING: This file is auto-derived from the mlkem-native source file
 *   dev/aarch64_opt/src/polyvec_basemul_acc_montgomery_cached_asm_k3.S using scripts/simpasm. Do not modify it directly.
 */


.text
.balign 4
#ifdef __APPLE__
.global _PQCP_MLKEM_NATIVE_MLKEM768_polyvec_basemul_acc_montgomery_cached_asm_k3
_PQCP_MLKEM_NATIVE_MLKEM768_polyvec_basemul_acc_montgomery_cached_asm_k3:
#else
.global PQCP_MLKEM_NATIVE_MLKEM768_polyvec_basemul_acc_montgomery_cached_asm_k3
PQCP_MLKEM_NATIVE_MLKEM768_polyvec_basemul_acc_montgomery_cached_asm_k3:
#endif

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
        mov	x13, #0x10              // =16
        ldr	q13, [x1, #0x10]
        ldr	q1, [x1], #0x20
        ldr	q3, [x2], #0x20
        ldur	q11, [x2, #-0x10]
        ldr	q17, [x4], #0x20
        ld1	{ v18.8h }, [x3], #16
        ldr	q27, [x5], #0x20
        ldur	q14, [x5, #-0x10]
        uzp2	v30.8h, v1.8h, v13.8h
        ldr	q9, [x8, #0x10]
        uzp1	v20.8h, v3.8h, v11.8h
        uzp1	v1.8h, v1.8h, v13.8h
        ldur	q29, [x4, #-0x10]
        ldr	q8, [x7], #0x20
        smull	v26.4s, v1.4h, v20.4h
        ldur	q21, [x7, #-0x10]
        smlal	v26.4s, v30.4h, v18.4h
        ld1	{ v7.8h }, [x6], #16
        smull2	v23.4s, v1.8h, v20.8h
        uzp1	v24.8h, v27.8h, v14.8h
        uzp2	v22.8h, v17.8h, v29.8h
        uzp1	v19.8h, v17.8h, v29.8h
        smlal2	v23.4s, v30.8h, v18.8h
        ldr	q31, [x8], #0x20
        uzp2	v13.8h, v3.8h, v11.8h
        smlal2	v23.4s, v19.8h, v24.8h
        ld1	{ v5.8h }, [x9], #16
        smlal	v26.4s, v19.4h, v24.4h
        uzp1	v15.8h, v8.8h, v21.8h
        smull	v18.4s, v1.4h, v13.4h
        smlal	v26.4s, v22.4h, v7.4h
        uzp1	v10.8h, v31.8h, v9.8h
        smlal2	v23.4s, v22.8h, v7.8h
        uzp2	v16.8h, v8.8h, v21.8h
        smlal2	v23.4s, v15.8h, v10.8h
        uzp2	v4.8h, v27.8h, v14.8h
        smlal2	v23.4s, v16.8h, v5.8h
        ld1	{ v25.8h }, [x3], #16
        smlal	v26.4s, v15.4h, v10.4h
        ldr	q21, [x4], #0x20
        ldr	q12, [x7, #0x10]
        smlal	v26.4s, v16.4h, v5.4h
        uzp2	v17.8h, v31.8h, v9.8h
        smlal	v18.4s, v30.4h, v20.4h
        ldr	q28, [x1, #0x10]
        smlal	v18.4s, v19.4h, v4.4h
        smlal	v18.4s, v22.4h, v24.4h
        smlal	v18.4s, v15.4h, v17.4h
        uzp1	v29.8h, v26.8h, v23.8h
        sub	x13, x13, #0x2

polyvec_basemul_acc_montgomery_cached_k3_loop_start:
        smull2	v8.4s, v1.8h, v13.8h
        ldur	q13, [x4, #-0x10]
        mul	v6.8h, v29.8h, v2.8h
        ldr	q11, [x1], #0x20
        ldr	q29, [x8, #0x10]
        ldr	q3, [x5], #0x20
        ldr	q7, [x8], #0x20
        smlal2	v8.4s, v30.8h, v20.8h
        ldr	q14, [x2], #0x20
        smlal	v18.4s, v16.4h, v10.4h
        uzp2	v30.8h, v11.8h, v28.8h
        smlal2	v8.4s, v19.8h, v4.8h
        smlal2	v23.4s, v6.8h, v0.8h
        ldur	q5, [x2, #-0x10]
        uzp1	v19.8h, v21.8h, v13.8h
        smlal2	v8.4s, v22.8h, v24.8h
        smlal	v26.4s, v6.4h, v0.4h
        ldur	q22, [x5, #-0x10]
        uzp1	v1.8h, v11.8h, v28.8h
        smlal2	v8.4s, v15.8h, v17.8h
        smlal2	v8.4s, v16.8h, v10.8h
        uzp1	v20.8h, v14.8h, v5.8h
        ldr	q27, [x7], #0x20
        ld1	{ v9.8h }, [x6], #16
        uzp2	v6.8h, v26.8h, v23.8h
        smull	v26.4s, v1.4h, v20.4h
        uzp1	v24.8h, v3.8h, v22.8h
        smull2	v23.4s, v1.8h, v20.8h
        smlal	v26.4s, v30.4h, v25.4h
        uzp1	v31.8h, v18.8h, v8.8h
        smlal	v26.4s, v19.4h, v24.4h
        uzp2	v4.8h, v3.8h, v22.8h
        uzp2	v22.8h, v21.8h, v13.8h
        mul	v11.8h, v31.8h, v2.8h
        uzp1	v15.8h, v27.8h, v12.8h
        smlal2	v23.4s, v30.8h, v25.8h
        uzp2	v16.8h, v27.8h, v12.8h
        smlal	v26.4s, v22.4h, v9.4h
        uzp1	v10.8h, v7.8h, v29.8h
        ld1	{ v31.8h }, [x9], #16
        smlal2	v23.4s, v19.8h, v24.8h
        smlal2	v8.4s, v11.8h, v0.8h
        uzp2	v13.8h, v14.8h, v5.8h
        smlal	v18.4s, v11.4h, v0.4h
        ldr	q28, [x1, #0x10]
        smlal2	v23.4s, v22.8h, v9.8h
        uzp2	v17.8h, v7.8h, v29.8h
        ld1	{ v25.8h }, [x3], #16
        smlal	v26.4s, v15.4h, v10.4h
        smlal2	v23.4s, v15.8h, v10.8h
        ldr	q21, [x4], #0x20
        uzp2	v29.8h, v18.8h, v8.8h
        smlal	v26.4s, v16.4h, v31.4h
        smlal2	v23.4s, v16.8h, v31.8h
        ldr	q12, [x7, #0x10]
        smull	v18.4s, v1.4h, v13.4h
        zip1	v8.8h, v6.8h, v29.8h
        zip2	v9.8h, v6.8h, v29.8h
        smlal	v18.4s, v30.4h, v20.4h
        str	q8, [x0], #0x20
        smlal	v18.4s, v19.4h, v4.4h
        stur	q9, [x0, #-0x10]
        smlal	v18.4s, v22.4h, v24.4h
        uzp1	v29.8h, v26.8h, v23.8h
        smlal	v18.4s, v15.4h, v17.4h
        subs	x13, x13, #0x1
        cbnz	x13, polyvec_basemul_acc_montgomery_cached_k3_loop_start
        ldr	q31, [x7], #0x20
        smull2	v8.4s, v1.8h, v13.8h
        ldr	q11, [x1], #0x20
        smlal2	v8.4s, v30.8h, v20.8h
        smlal2	v8.4s, v19.8h, v4.8h
        ldr	q9, [x2], #0x20
        smlal2	v8.4s, v22.8h, v24.8h
        ldur	q7, [x2, #-0x10]
        smlal2	v8.4s, v15.8h, v17.8h
        ld1	{ v14.8h }, [x6], #16
        smlal	v18.4s, v16.4h, v10.4h
        uzp1	v3.8h, v11.8h, v28.8h
        uzp2	v24.8h, v11.8h, v28.8h
        mul	v1.8h, v29.8h, v2.8h
        uzp2	v13.8h, v9.8h, v7.8h
        ldr	q4, [x5], #0x20
        uzp1	v27.8h, v9.8h, v7.8h
        smlal2	v8.4s, v16.8h, v10.8h
        ldur	q9, [x5, #-0x10]
        smull2	v30.4s, v3.8h, v13.8h
        smull	v20.4s, v3.4h, v13.4h
        ldur	q13, [x4, #-0x10]
        smull2	v17.4s, v3.8h, v27.8h
        ldr	q16, [x8, #0x10]
        smlal2	v17.4s, v24.8h, v25.8h
        smlal	v20.4s, v24.4h, v27.4h
        uzp2	v15.8h, v4.8h, v9.8h
        smull	v11.4s, v3.4h, v27.4h
        uzp1	v3.8h, v4.8h, v9.8h
        smlal	v11.4s, v24.4h, v25.4h
        uzp1	v6.8h, v21.8h, v13.8h
        smlal2	v30.4s, v24.8h, v27.8h
        uzp2	v13.8h, v21.8h, v13.8h
        smlal2	v17.4s, v6.8h, v3.8h
        ldr	q7, [x8], #0x20
        smlal2	v30.4s, v6.8h, v15.8h
        ld1	{ v25.8h }, [x9], #16
        smlal	v20.4s, v6.4h, v15.4h
        uzp1	v15.8h, v18.8h, v8.8h
        smlal2	v30.4s, v13.8h, v3.8h
        uzp1	v4.8h, v31.8h, v12.8h
        smlal	v11.4s, v6.4h, v3.4h
        uzp1	v19.8h, v7.8h, v16.8h
        smlal	v20.4s, v13.4h, v3.4h
        uzp2	v27.8h, v31.8h, v12.8h
        uzp2	v22.8h, v7.8h, v16.8h
        smlal2	v17.4s, v13.8h, v14.8h
        smlal2	v17.4s, v4.8h, v19.8h
        smlal2	v30.4s, v4.8h, v22.8h
        smlal	v20.4s, v4.4h, v22.4h
        smlal	v11.4s, v13.4h, v14.4h
        mul	v22.8h, v15.8h, v2.8h
        smlal2	v30.4s, v27.8h, v19.8h
        smlal	v20.4s, v27.4h, v19.4h
        smlal	v11.4s, v4.4h, v19.4h
        smlal	v11.4s, v27.4h, v25.4h
        smlal2	v17.4s, v27.8h, v25.8h
        smlal	v18.4s, v22.4h, v0.4h
        uzp1	v7.8h, v20.8h, v30.8h
        smlal2	v8.4s, v22.8h, v0.8h
        mul	v3.8h, v7.8h, v2.8h
        uzp1	v12.8h, v11.8h, v17.8h
        smlal	v26.4s, v1.4h, v0.4h
        uzp2	v15.8h, v18.8h, v8.8h
        mul	v19.8h, v12.8h, v2.8h
        smlal	v20.4s, v3.4h, v0.4h
        smlal2	v30.4s, v3.8h, v0.8h
        smlal2	v23.4s, v1.8h, v0.8h
        smlal2	v17.4s, v19.8h, v0.8h
        smlal	v11.4s, v19.4h, v0.4h
        uzp2	v8.8h, v20.8h, v30.8h
        uzp2	v4.8h, v26.8h, v23.8h
        uzp2	v13.8h, v11.8h, v17.8h
        zip2	v26.8h, v4.8h, v15.8h
        zip1	v14.8h, v4.8h, v15.8h
        zip1	v23.8h, v13.8h, v8.8h
        zip2	v13.8h, v13.8h, v8.8h
        str	q26, [x0, #0x10]
        str	q14, [x0], #0x20
        str	q23, [x0], #0x20
        stur	q13, [x0, #-0x10]
        ldp	d8, d9, [sp]
        ldp	d10, d11, [sp, #0x10]
        ldp	d12, d13, [sp, #0x20]
        ldp	d14, d15, [sp, #0x30]
        add	sp, sp, #0x40
        ret
