/* Copyright (c) 2022 Arm Limited
 * Copyright (c) 2022 Hanno Becker
 * Copyright (c) 2023 Amin Abdulrahman, Matthias Kannwischer
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
 *
 * - [SLOTHY_Paper]
 *   Fast and Clean: Auditable high-performance assembly via constraint solving
 *   Abdulrahman, Becker, Kannwischer, Klein
 *   https://eprint.iacr.org/2022/1303
 */

/*yaml
  Name: intt_asm
  Description: AArch64 ML-KEM inverse NTT following @[NeonNTT] and @[SLOTHY_Paper]
  Signature: void mlk_intt_asm(int16_t p[256], const int16_t twiddles12345[80], const int16_t twiddles56[384])
  ABI:
    x0:
      type: buffer
      size_bytes: 512
      permissions: read/write
      c_parameter: int16_t p[256]
      description: Input/output polynomial
    x1:
      type: buffer
      size_bytes: 160
      permissions: read-only
      c_parameter: const int16_t twiddles12345[80]
      description: Twiddle factors for layers 1-5
    x2:
      type: buffer
      size_bytes: 768
      permissions: read-only
      c_parameter: const int16_t twiddles56[384]
      description: Twiddle factors for layers 6-7
  Stack:
    bytes: 64
    description: saving callee-saved Neon registers
*/

#include "../../../common.h"
#if defined(MLK_ARITH_BACKEND_AARCH64) &&  !defined(MLK_CONFIG_MULTILEVEL_NO_SHARED)

/*
 * WARNING: This file is auto-derived from the mlkem-native source file
 *   dev/aarch64_opt/src/intt.S using scripts/simpasm. Do not modify it directly.
 */


.text
.balign 4
.global MLK_ASM_NAMESPACE(intt_asm)
MLK_ASM_FN_SYMBOL(intt_asm)

        sub	sp, sp, #0x40
        stp	d8, d9, [sp]
        stp	d10, d11, [sp, #0x10]
        stp	d12, d13, [sp, #0x20]
        stp	d14, d15, [sp, #0x30]
        mov	w5, #0xd01              // =3329
        mov	v7.h[0], w5
        mov	w5, #0x4ebf             // =20159
        mov	v7.h[1], w5
        mov	w5, #0x200              // =512
        dup	v29.8h, w5
        mov	w5, #0x13b0             // =5040
        dup	v30.8h, w5
        mov	x3, x0
        mov	x4, #0x8                // =8
        ldr	q27, [x3]
        ldr	q19, [x3, #0x10]
        ldr	q16, [x3, #0x30]
        trn2	v8.4s, v27.4s, v19.4s
        trn1	v18.4s, v27.4s, v19.4s
        ldr	q5, [x3, #0x20]
        ldr	q14, [x2, #0x40]
        trn2	v12.4s, v5.4s, v16.4s
        trn1	v25.4s, v5.4s, v16.4s
        ldr	q21, [x2, #0x10]
        trn2	v15.2d, v8.2d, v12.2d
        trn1	v3.2d, v8.2d, v12.2d
        trn1	v11.2d, v18.2d, v25.2d
        trn2	v2.2d, v18.2d, v25.2d
        sub	v8.8h, v11.8h, v3.8h
        sub	v24.8h, v2.8h, v15.8h
        ldr	q28, [x2, #0x50]
        mul	v22.8h, v24.8h, v14.8h
        ldr	q5, [x2, #0x20]
        ldr	q17, [x2, #0x30]
        ldr	q6, [x3, #0x60]
        add	v0.8h, v2.8h, v15.8h
        ldr	q19, [x3, #0x40]
        add	v2.8h, v11.8h, v3.8h
        ldr	q23, [x3, #0x50]
        ldr	q9, [x3, #0x70]
        mul	v15.8h, v8.8h, v5.8h
        sqrdmulh	v10.8h, v8.8h, v17.8h
        sqrdmulh	v17.8h, v24.8h, v28.8h
        trn2	v14.4s, v6.4s, v9.4s
        trn2	v20.4s, v19.4s, v23.4s
        trn1	v25.4s, v19.4s, v23.4s
        mls	v22.8h, v17.8h, v7.h[0]
        mls	v15.8h, v10.8h, v7.h[0]
        trn1	v4.4s, v6.4s, v9.4s
        mul	v1.8h, v2.8h, v29.8h
        mul	v23.8h, v0.8h, v29.8h
        sqrdmulh	v5.8h, v0.8h, v30.8h
        sqrdmulh	v13.8h, v15.8h, v30.8h
        sqrdmulh	v11.8h, v22.8h, v30.8h
        sqrdmulh	v12.8h, v2.8h, v30.8h
        mul	v19.8h, v22.8h, v29.8h
        mul	v0.8h, v15.8h, v29.8h
        trn1	v15.2d, v25.2d, v4.2d
        trn2	v22.2d, v25.2d, v4.2d
        trn2	v24.2d, v20.2d, v14.2d
        mls	v0.8h, v13.8h, v7.h[0]
        mls	v23.8h, v5.8h, v7.h[0]
        sub	v10.8h, v22.8h, v24.8h
        trn1	v31.2d, v20.2d, v14.2d
        mls	v1.8h, v12.8h, v7.h[0]
        mls	v19.8h, v11.8h, v7.h[0]
        ldr	q13, [x2, #0x90]
        ldr	q14, [x2, #0xa0]
        ldr	q5, [x2, #0x80]
        ldr	q2, [x2, #0xb0]
        ldr	q25, [x2], #0x60
        sub	v9.8h, v15.8h, v31.8h
        add	v15.8h, v15.8h, v31.8h
        sub	v28.8h, v1.8h, v23.8h
        sqrdmulh	v26.8h, v9.8h, v13.8h
        mul	v11.8h, v9.8h, v5.8h
        mul	v14.8h, v10.8h, v14.8h
        sub	v4.8h, v0.8h, v19.8h
        sqrdmulh	v6.8h, v10.8h, v2.8h
        mls	v11.8h, v26.8h, v7.h[0]
        mul	v9.8h, v28.8h, v25.8h
        sqrdmulh	v18.8h, v4.8h, v21.8h
        sqrdmulh	v16.8h, v28.8h, v21.8h
        mul	v20.8h, v4.8h, v25.8h
        mls	v14.8h, v6.8h, v7.h[0]
        add	v21.8h, v22.8h, v24.8h
        mul	v17.8h, v15.8h, v29.8h
        mls	v20.8h, v18.8h, v7.h[0]
        mls	v9.8h, v16.8h, v7.h[0]
        mul	v24.8h, v21.8h, v29.8h
        mul	v16.8h, v11.8h, v29.8h
        mul	v22.8h, v14.8h, v29.8h
        sqrdmulh	v13.8h, v21.8h, v30.8h
        add	v10.8h, v0.8h, v19.8h
        add	v23.8h, v1.8h, v23.8h
        sqrdmulh	v15.8h, v15.8h, v30.8h
        sqrdmulh	v26.8h, v14.8h, v30.8h
        sqrdmulh	v11.8h, v11.8h, v30.8h
        mls	v24.8h, v13.8h, v7.h[0]
        mls	v17.8h, v15.8h, v7.h[0]
        mls	v22.8h, v26.8h, v7.h[0]
        ldr	q28, [x2], #0x60
        trn1	v6.4s, v9.4s, v20.4s
        trn2	v21.4s, v9.4s, v20.4s
        trn2	v1.4s, v23.4s, v10.4s
        trn1	v25.4s, v23.4s, v10.4s
        ldur	q10, [x2, #-0x50]
        sub	v4.8h, v17.8h, v24.8h
        mls	v16.8h, v11.8h, v7.h[0]
        add	v14.8h, v17.8h, v24.8h
        sqrdmulh	v23.8h, v4.8h, v10.8h
        trn1	v0.2d, v25.2d, v6.2d
        trn2	v2.2d, v1.2d, v21.2d
        trn1	v11.2d, v1.2d, v21.2d
        trn2	v15.2d, v25.2d, v6.2d
        add	v6.8h, v0.8h, v11.8h
        add	v26.8h, v15.8h, v2.8h
        sub	v18.8h, v16.8h, v22.8h
        mul	v4.8h, v4.8h, v28.8h
        sub	v19.8h, v6.8h, v26.8h
        mul	v12.8h, v18.8h, v28.8h
        add	v8.8h, v6.8h, v26.8h
        add	v28.8h, v16.8h, v22.8h
        sqrdmulh	v1.8h, v18.8h, v10.8h
        mls	v4.8h, v23.8h, v7.h[0]
        sqdmulh	v21.8h, v8.8h, v7.h[1]
        trn1	v5.4s, v14.4s, v28.4s
        mls	v12.8h, v1.8h, v7.h[0]
        sub	v15.8h, v15.8h, v2.8h
        srshr	v18.8h, v21.8h, #0xb
        sub	v20.8h, v0.8h, v11.8h
        trn2	v26.4s, v4.4s, v12.4s
        trn2	v14.4s, v14.4s, v28.4s
        mls	v8.8h, v18.8h, v7.h[0]
        trn1	v10.4s, v4.4s, v12.4s
        trn1	v24.2d, v14.2d, v26.2d
        trn2	v1.2d, v14.2d, v26.2d
        trn1	v3.2d, v5.2d, v10.2d
        str	q8, [x3], #0x40
        trn2	v23.2d, v5.2d, v10.2d
        add	v12.8h, v3.8h, v24.8h
        add	v9.8h, v23.8h, v1.8h
        sub	x4, x4, #0x2

intt_layer4567_start:
        ldr	q10, [x1], #0x10
        ldr	q26, [x3, #0x50]
        sqrdmulh	v22.8h, v19.8h, v10.h[1]
        mul	v18.8h, v19.8h, v10.h[0]
        ldr	q2, [x3, #0x40]
        mul	v5.8h, v15.8h, v10.h[4]
        mls	v18.8h, v22.8h, v7.h[0]
        trn1	v14.4s, v2.4s, v26.4s
        trn2	v11.4s, v2.4s, v26.4s
        sqrdmulh	v21.8h, v15.8h, v10.h[5]
        sub	v15.8h, v23.8h, v1.8h
        ldr	q23, [x2, #0x50]
        ldr	q22, [x3, #0x60]
        ldr	q26, [x2, #0x40]
        ldr	q17, [x3, #0x70]
        ldr	q0, [x2, #0x30]
        trn1	v6.4s, v22.4s, v17.4s
        trn2	v13.4s, v22.4s, v17.4s
        mls	v5.8h, v21.8h, v7.h[0]
        trn2	v16.2d, v14.2d, v6.2d
        trn1	v2.2d, v14.2d, v6.2d
        trn2	v31.2d, v11.2d, v13.2d
        trn1	v11.2d, v11.2d, v13.2d
        sub	v14.8h, v16.8h, v31.8h
        add	v28.8h, v2.8h, v11.8h
        sub	v25.8h, v2.8h, v11.8h
        sqrdmulh	v19.8h, v14.8h, v23.8h
        ldr	q8, [x2, #0x20]
        mul	v23.8h, v14.8h, v26.8h
        add	v17.8h, v16.8h, v31.8h
        sqrdmulh	v27.8h, v25.8h, v0.8h
        sqrdmulh	v16.8h, v20.8h, v10.h[3]
        mul	v22.8h, v25.8h, v8.8h
        mul	v26.8h, v17.8h, v29.8h
        mls	v23.8h, v19.8h, v7.h[0]
        mul	v4.8h, v20.8h, v10.h[2]
        mls	v22.8h, v27.8h, v7.h[0]
        ldr	q13, [x2, #0x10]
        sqrdmulh	v20.8h, v23.8h, v30.8h
        sqrdmulh	v1.8h, v28.8h, v30.8h
        mul	v0.8h, v28.8h, v29.8h
        mul	v8.8h, v22.8h, v29.8h
        ldr	q14, [x2], #0x60
        mul	v31.8h, v23.8h, v29.8h
        sqrdmulh	v28.8h, v22.8h, v30.8h
        stur	q18, [x3, #-0x20]
        sqrdmulh	v22.8h, v17.8h, v30.8h
        mls	v4.8h, v16.8h, v7.h[0]
        sub	v19.8h, v12.8h, v9.8h
        mls	v31.8h, v20.8h, v7.h[0]
        sub	v20.8h, v3.8h, v24.8h
        mls	v0.8h, v1.8h, v7.h[0]
        mls	v8.8h, v28.8h, v7.h[0]
        sub	v18.8h, v4.8h, v5.8h
        mls	v26.8h, v22.8h, v7.h[0]
        add	v1.8h, v4.8h, v5.8h
        add	v17.8h, v8.8h, v31.8h
        add	v23.8h, v12.8h, v9.8h
        sub	v2.8h, v8.8h, v31.8h
        sqrdmulh	v31.8h, v18.8h, v10.h[1]
        sqdmulh	v28.8h, v23.8h, v7.h[1]
        mul	v8.8h, v2.8h, v14.8h
        sqrdmulh	v21.8h, v2.8h, v13.8h
        mul	v2.8h, v18.8h, v10.h[0]
        srshr	v22.8h, v28.8h, #0xb
        sub	v28.8h, v0.8h, v26.8h
        add	v10.8h, v0.8h, v26.8h
        stur	q1, [x3, #-0x30]
        mul	v18.8h, v28.8h, v14.8h
        sqrdmulh	v11.8h, v28.8h, v13.8h
        mls	v23.8h, v22.8h, v7.h[0]
        mls	v8.8h, v21.8h, v7.h[0]
        trn2	v27.4s, v10.4s, v17.4s
        mls	v18.8h, v11.8h, v7.h[0]
        mls	v2.8h, v31.8h, v7.h[0]
        trn1	v31.4s, v10.4s, v17.4s
        str	q23, [x3], #0x40
        trn1	v21.4s, v18.4s, v8.4s
        stur	q2, [x3, #-0x50]
        trn2	v4.4s, v18.4s, v8.4s
        trn2	v23.2d, v31.2d, v21.2d
        trn1	v3.2d, v31.2d, v21.2d
        trn2	v1.2d, v27.2d, v4.2d
        trn1	v24.2d, v27.2d, v4.2d
        add	v9.8h, v23.8h, v1.8h
        add	v12.8h, v3.8h, v24.8h
        subs	x4, x4, #0x1
        cbnz	x4, intt_layer4567_start
        ldr	q2, [x1], #0x10
        sub	v10.8h, v23.8h, v1.8h
        sub	v1.8h, v12.8h, v9.8h
        mul	v18.8h, v19.8h, v2.h[0]
        sqrdmulh	v31.8h, v19.8h, v2.h[1]
        mul	v6.8h, v15.8h, v2.h[4]
        sqrdmulh	v21.8h, v15.8h, v2.h[5]
        sqrdmulh	v13.8h, v20.8h, v2.h[3]
        mls	v18.8h, v31.8h, v7.h[0]
        mul	v15.8h, v20.8h, v2.h[2]
        mls	v6.8h, v21.8h, v7.h[0]
        add	v20.8h, v12.8h, v9.8h
        sub	v25.8h, v3.8h, v24.8h
        mls	v15.8h, v13.8h, v7.h[0]
        sqdmulh	v13.8h, v20.8h, v7.h[1]
        ldr	q5, [x1], #0x10
        sub	v9.8h, v15.8h, v6.8h
        add	v12.8h, v15.8h, v6.8h
        srshr	v21.8h, v13.8h, #0xb
        sqrdmulh	v31.8h, v9.8h, v2.h[1]
        mul	v15.8h, v9.8h, v2.h[0]
        stur	q12, [x3, #-0x30]
        mul	v12.8h, v10.8h, v5.h[4]
        sqrdmulh	v10.8h, v10.8h, v5.h[5]
        sqrdmulh	v13.8h, v25.8h, v5.h[3]
        mul	v6.8h, v25.8h, v5.h[2]
        mls	v20.8h, v21.8h, v7.h[0]
        mls	v15.8h, v31.8h, v7.h[0]
        mls	v12.8h, v10.8h, v7.h[0]
        mls	v6.8h, v13.8h, v7.h[0]
        sqrdmulh	v13.8h, v1.8h, v5.h[1]
        mul	v9.8h, v1.8h, v5.h[0]
        str	q20, [x3], #0x40
        sub	v10.8h, v6.8h, v12.8h
        stur	q15, [x3, #-0x50]
        mls	v9.8h, v13.8h, v7.h[0]
        sqrdmulh	v13.8h, v10.8h, v5.h[1]
        mul	v3.8h, v10.8h, v5.h[0]
        stur	q18, [x3, #-0x60]
        add	v10.8h, v6.8h, v12.8h
        stur	q9, [x3, #-0x20]
        mls	v3.8h, v13.8h, v7.h[0]
        stur	q10, [x3, #-0x30]
        stur	q3, [x3, #-0x10]
        mov	x4, #0x4                // =4
        ldr	q0, [x1], #0x20
        ldur	q1, [x1, #-0x10]
        ldr	q14, [x0, #0x80]
        ldr	q21, [x0, #0xc0]
        ldr	q31, [x0, #0x1c0]
        sub	v26.8h, v14.8h, v21.8h
        add	v25.8h, v14.8h, v21.8h
        ldr	q27, [x0, #0x40]
        ldr	q14, [x0, #0x180]
        ldr	q16, [x0, #0x140]
        sub	v22.8h, v14.8h, v31.8h
        add	v4.8h, v14.8h, v31.8h
        ldr	q31, [x0]
        mul	v18.8h, v26.8h, v1.h[0]
        sqrdmulh	v8.8h, v26.8h, v1.h[1]
        add	v28.8h, v31.8h, v27.8h
        sub	v10.8h, v31.8h, v27.8h
        sqrdmulh	v13.8h, v22.8h, v1.h[5]
        sub	v30.8h, v28.8h, v25.8h
        add	v17.8h, v28.8h, v25.8h
        ldr	q5, [x0, #0x100]
        mul	v31.8h, v22.8h, v1.h[4]
        mul	v26.8h, v10.8h, v0.h[6]
        add	v6.8h, v5.8h, v16.8h
        sub	v15.8h, v5.8h, v16.8h
        sqrdmulh	v19.8h, v10.8h, v0.h[7]
        add	v12.8h, v6.8h, v4.8h
        sub	v29.8h, v6.8h, v4.8h
        mul	v25.8h, v15.8h, v1.h[2]
        ldr	q22, [x0, #0xd0]
        mls	v18.8h, v8.8h, v7.h[0]
        ldr	q5, [x0, #0x10]
        sqrdmulh	v8.8h, v15.8h, v1.h[3]
        ldr	q20, [x0, #0x1d0]
        ldr	q15, [x0, #0x110]
        mls	v31.8h, v13.8h, v7.h[0]
        ldr	q16, [x0, #0x50]
        sqdmulh	v6.8h, v17.8h, v7.h[1]
        ldr	q23, [x0, #0x90]
        mul	v21.8h, v30.8h, v0.h[2]
        srshr	v3.8h, v6.8h, #0xb
        sqrdmulh	v11.8h, v30.8h, v0.h[3]
        sub	v27.8h, v5.8h, v16.8h
        mls	v17.8h, v3.8h, v7.h[0]
        mls	v26.8h, v19.8h, v7.h[0]
        mls	v25.8h, v8.8h, v7.h[0]
        sub	v19.8h, v23.8h, v22.8h
        mul	v14.8h, v27.8h, v0.h[6]
        ldr	q28, [x0, #0x150]
        add	v4.8h, v26.8h, v18.8h
        sub	v18.8h, v26.8h, v18.8h
        ldr	q30, [x0, #0x190]
        sub	v13.8h, v17.8h, v12.8h
        add	v8.8h, v17.8h, v12.8h
        mul	v3.8h, v29.8h, v0.h[4]
        sqrdmulh	v17.8h, v29.8h, v0.h[5]
        add	v9.8h, v23.8h, v22.8h
        sub	v12.8h, v25.8h, v31.8h
        sub	v2.8h, v15.8h, v28.8h
        sub	v29.8h, v30.8h, v20.8h
        sqrdmulh	v6.8h, v27.8h, v0.h[7]
        sqrdmulh	v23.8h, v19.8h, v1.h[1]
        add	v27.8h, v5.8h, v16.8h
        mul	v26.8h, v19.8h, v1.h[0]
        sqrdmulh	v24.8h, v12.8h, v0.h[5]
        mul	v19.8h, v2.8h, v1.h[2]
        mul	v16.8h, v18.8h, v0.h[2]
        sqrdmulh	v5.8h, v29.8h, v1.h[5]
        add	v20.8h, v30.8h, v20.8h
        sqrdmulh	v30.8h, v2.8h, v1.h[3]
        mul	v2.8h, v29.8h, v1.h[4]
        mls	v14.8h, v6.8h, v7.h[0]
        add	v29.8h, v15.8h, v28.8h
        sqrdmulh	v28.8h, v18.8h, v0.h[3]
        mls	v19.8h, v30.8h, v7.h[0]
        mls	v26.8h, v23.8h, v7.h[0]
        add	v10.8h, v25.8h, v31.8h
        mls	v2.8h, v5.8h, v7.h[0]
        mls	v21.8h, v11.8h, v7.h[0]
        sub	v25.8h, v29.8h, v20.8h
        mul	v23.8h, v12.8h, v0.h[4]
        mls	v16.8h, v28.8h, v7.h[0]
        mls	v3.8h, v17.8h, v7.h[0]
        mul	v18.8h, v13.8h, v0.h[0]
        mul	v17.8h, v25.8h, v0.h[4]
        sqrdmulh	v11.8h, v25.8h, v0.h[5]
        sub	v31.8h, v19.8h, v2.8h
        sqrdmulh	v28.8h, v13.8h, v0.h[1]
        add	v12.8h, v21.8h, v3.8h
        sub	v6.8h, v21.8h, v3.8h
        sub	v21.8h, v27.8h, v9.8h
        sqrdmulh	v13.8h, v31.8h, v0.h[5]
        sub	v25.8h, v14.8h, v26.8h
        mul	v3.8h, v31.8h, v0.h[4]
        mls	v17.8h, v11.8h, v7.h[0]
        mls	v23.8h, v24.8h, v7.h[0]
        sqrdmulh	v24.8h, v25.8h, v0.h[3]
        mul	v15.8h, v25.8h, v0.h[2]
        sqrdmulh	v5.8h, v21.8h, v0.h[3]
        add	v11.8h, v16.8h, v23.8h
        mls	v3.8h, v13.8h, v7.h[0]
        sub	v30.8h, v16.8h, v23.8h
        mls	v15.8h, v24.8h, v7.h[0]
        str	q11, [x0, #0xc0]
        add	v23.8h, v27.8h, v9.8h
        sqrdmulh	v16.8h, v30.8h, v0.h[1]
        add	v24.8h, v4.8h, v10.8h
        sub	v13.8h, v15.8h, v3.8h
        str	q8, [x0], #0x10
        mul	v8.8h, v30.8h, v0.h[0]
        mls	v18.8h, v28.8h, v7.h[0]
        str	q12, [x0, #0x70]
        add	v20.8h, v29.8h, v20.8h
        mls	v8.8h, v16.8h, v7.h[0]
        add	v3.8h, v15.8h, v3.8h
        str	q24, [x0, #0x30]
        sqrdmulh	v12.8h, v6.8h, v0.h[1]
        str	q8, [x0, #0x1b0]
        sub	x4, x4, #0x2

intt_layer123_start:
        str	q18, [x0, #0xf0]
        sqdmulh	v24.8h, v23.8h, v7.h[1]
        ldr	q18, [x0, #0x90]
        sub	v16.8h, v4.8h, v10.8h
        srshr	v4.8h, v24.8h, #0xb
        ldr	q10, [x0, #0xd0]
        mls	v23.8h, v4.8h, v7.h[0]
        add	v4.8h, v14.8h, v26.8h
        sub	v8.8h, v18.8h, v10.8h
        add	v29.8h, v18.8h, v10.8h
        sub	v22.8h, v23.8h, v20.8h
        mul	v26.8h, v8.8h, v1.h[0]
        sqrdmulh	v11.8h, v8.8h, v1.h[1]
        ldr	q28, [x0, #0x10]
        add	v24.8h, v23.8h, v20.8h
        mls	v26.8h, v11.8h, v7.h[0]
        ldr	q27, [x0, #0x50]
        sqrdmulh	v9.8h, v22.8h, v0.h[1]
        mul	v8.8h, v21.8h, v0.h[2]
        mul	v23.8h, v6.8h, v0.h[0]
        mul	v18.8h, v22.8h, v0.h[0]
        add	v20.8h, v28.8h, v27.8h
        sub	v31.8h, v28.8h, v27.8h
        mls	v23.8h, v12.8h, v7.h[0]
        sub	v21.8h, v20.8h, v29.8h
        sqrdmulh	v30.8h, v31.8h, v0.h[7]
        mul	v11.8h, v16.8h, v0.h[0]
        str	q23, [x0, #0x170]
        add	v23.8h, v20.8h, v29.8h
        sqrdmulh	v20.8h, v16.8h, v0.h[1]
        str	q24, [x0], #0x10
        mul	v14.8h, v31.8h, v0.h[6]
        mls	v8.8h, v5.8h, v7.h[0]
        ldr	q24, [x0, #0x1c0]
        ldr	q15, [x0, #0x140]
        ldr	q22, [x0, #0x100]
        mls	v18.8h, v9.8h, v7.h[0]
        ldr	q25, [x0, #0x180]
        mls	v11.8h, v20.8h, v7.h[0]
        mls	v14.8h, v30.8h, v7.h[0]
        add	v5.8h, v22.8h, v15.8h
        sub	v6.8h, v8.8h, v17.8h
        add	v28.8h, v25.8h, v24.8h
        add	v10.8h, v19.8h, v2.8h
        sub	v30.8h, v22.8h, v15.8h
        sub	v25.8h, v25.8h, v24.8h
        sub	v29.8h, v5.8h, v28.8h
        mul	v19.8h, v30.8h, v1.h[2]
        mul	v2.8h, v25.8h, v1.h[4]
        sqrdmulh	v27.8h, v30.8h, v1.h[3]
        sqrdmulh	v31.8h, v25.8h, v1.h[5]
        sqrdmulh	v24.8h, v29.8h, v0.h[5]
        add	v15.8h, v8.8h, v17.8h
        mul	v17.8h, v29.8h, v0.h[4]
        mls	v2.8h, v31.8h, v7.h[0]
        str	q15, [x0, #0x70]
        mls	v19.8h, v27.8h, v7.h[0]
        str	q11, [x0, #0x120]
        add	v20.8h, v5.8h, v28.8h
        add	v11.8h, v4.8h, v10.8h
        sqrdmulh	v12.8h, v6.8h, v0.h[1]
        sqrdmulh	v5.8h, v21.8h, v0.h[3]
        sub	v25.8h, v14.8h, v26.8h
        sub	v22.8h, v19.8h, v2.8h
        sqrdmulh	v28.8h, v13.8h, v0.h[1]
        mul	v29.8h, v25.8h, v0.h[2]
        mul	v16.8h, v22.8h, v0.h[4]
        sqrdmulh	v27.8h, v22.8h, v0.h[5]
        sqrdmulh	v15.8h, v25.8h, v0.h[3]
        mul	v8.8h, v13.8h, v0.h[0]
        str	q3, [x0, #0xb0]
        mls	v16.8h, v27.8h, v7.h[0]
        mls	v29.8h, v15.8h, v7.h[0]
        mls	v8.8h, v28.8h, v7.h[0]
        mls	v17.8h, v24.8h, v7.h[0]
        str	q11, [x0, #0x30]
        add	v3.8h, v29.8h, v16.8h
        str	q8, [x0, #0x1b0]
        sub	v13.8h, v29.8h, v16.8h
        subs	x4, x4, #0x1
        cbnz	x4, intt_layer123_start
        add	v8.8h, v14.8h, v26.8h
        add	v15.8h, v19.8h, v2.8h
        str	q18, [x0, #0xf0]
        sub	v28.8h, v4.8h, v10.8h
        mul	v29.8h, v21.8h, v0.h[2]
        str	q3, [x0, #0xc0]
        sqrdmulh	v14.8h, v13.8h, v0.h[1]
        mul	v13.8h, v13.8h, v0.h[0]
        mul	v21.8h, v6.8h, v0.h[0]
        mls	v29.8h, v5.8h, v7.h[0]
        sqdmulh	v3.8h, v23.8h, v7.h[1]
        add	v10.8h, v8.8h, v15.8h
        mls	v21.8h, v12.8h, v7.h[0]
        add	v30.8h, v29.8h, v17.8h
        srshr	v11.8h, v3.8h, #0xb
        sub	v29.8h, v29.8h, v17.8h
        sub	v2.8h, v8.8h, v15.8h
        mls	v23.8h, v11.8h, v7.h[0]
        mls	v13.8h, v14.8h, v7.h[0]
        sqrdmulh	v19.8h, v28.8h, v0.h[1]
        mul	v17.8h, v28.8h, v0.h[0]
        add	v14.8h, v23.8h, v20.8h
        sub	v25.8h, v23.8h, v20.8h
        str	q10, [x0, #0x40]
        sqrdmulh	v4.8h, v29.8h, v0.h[1]
        str	q21, [x0, #0x170]
        sqrdmulh	v20.8h, v2.8h, v0.h[1]
        str	q30, [x0, #0x80]
        mul	v10.8h, v29.8h, v0.h[0]
        sqrdmulh	v21.8h, v25.8h, v0.h[1]
        mls	v17.8h, v19.8h, v7.h[0]
        str	q14, [x0], #0x10
        mul	v18.8h, v2.8h, v0.h[0]
        mls	v10.8h, v4.8h, v7.h[0]
        str	q17, [x0, #0x120]
        mul	v19.8h, v25.8h, v0.h[0]
        str	q13, [x0, #0x1b0]
        mls	v18.8h, v20.8h, v7.h[0]
        str	q10, [x0, #0x170]
        mls	v19.8h, v21.8h, v7.h[0]
        str	q18, [x0, #0x130]
        str	q19, [x0, #0xf0]
        ldp	d8, d9, [sp]
        ldp	d10, d11, [sp, #0x10]
        ldp	d12, d13, [sp, #0x20]
        ldp	d14, d15, [sp, #0x30]
        add	sp, sp, #0x40
        ret

#endif /* MLK_ARITH_BACKEND_AARCH64 && !MLK_CONFIG_MULTILEVEL_NO_SHARED */
