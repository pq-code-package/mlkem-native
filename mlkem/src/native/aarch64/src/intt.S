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

        .cfi_startproc
        sub	sp, sp, #0x40
        .cfi_adjust_cfa_offset 0x40
        stp	d8, d9, [sp]
        .cfi_rel_offset d8, 0x0
        .cfi_rel_offset d9, 0x8
        stp	d10, d11, [sp, #0x10]
        .cfi_rel_offset d10, 0x10
        .cfi_rel_offset d11, 0x18
        stp	d12, d13, [sp, #0x20]
        .cfi_rel_offset d12, 0x20
        .cfi_rel_offset d13, 0x28
        stp	d14, d15, [sp, #0x30]
        .cfi_rel_offset d14, 0x30
        .cfi_rel_offset d15, 0x38
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
        ldr	q16, [x3]
        ldr	q19, [x3, #0x10]
        ldr	q21, [x3, #0x30]
        ldr	q23, [x2, #0x40]
        ldr	q6, [x3, #0x20]
        ldr	q3, [x3, #0x50]
        ldr	q28, [x2, #0x20]
        ldr	q26, [x2, #0x30]
        sqrdmulh	v0.8h, v16.8h, v30.8h
        ldr	q9, [x2], #0x60
        ldr	q8, [x3, #0x70]
        mul	v16.8h, v16.8h, v29.8h
        ldr	q11, [x3, #0x60]
        ldur	q20, [x2, #-0x10]
        sqrdmulh	v24.8h, v19.8h, v30.8h
        ldur	q25, [x2, #-0x50]
        mul	v22.8h, v19.8h, v29.8h
        sqrdmulh	v19.8h, v21.8h, v30.8h
        mul	v1.8h, v21.8h, v29.8h
        ldr	q21, [x3, #0x40]
        mul	v4.8h, v6.8h, v29.8h
        sqrdmulh	v13.8h, v6.8h, v30.8h
        mls	v16.8h, v0.8h, v7.h[0]
        mls	v22.8h, v24.8h, v7.h[0]
        mls	v4.8h, v13.8h, v7.h[0]
        mls	v1.8h, v19.8h, v7.h[0]
        trn1	v24.4s, v16.4s, v22.4s
        sqrdmulh	v2.8h, v11.8h, v30.8h
        trn2	v15.4s, v16.4s, v22.4s
        mul	v18.8h, v11.8h, v29.8h
        trn2	v22.4s, v4.4s, v1.4s
        trn1	v5.4s, v4.4s, v1.4s
        sqrdmulh	v13.8h, v8.8h, v30.8h
        trn2	v27.2d, v15.2d, v22.2d
        mls	v18.8h, v2.8h, v7.h[0]
        trn2	v10.2d, v24.2d, v5.2d
        trn1	v14.2d, v15.2d, v22.2d
        sub	v19.8h, v10.8h, v27.8h
        sqrdmulh	v22.8h, v3.8h, v30.8h
        trn1	v12.2d, v24.2d, v5.2d
        sqrdmulh	v6.8h, v19.8h, v20.8h
        add	v0.8h, v10.8h, v27.8h
        sub	v31.8h, v12.8h, v14.8h
        mul	v16.8h, v19.8h, v23.8h
        add	v1.8h, v12.8h, v14.8h
        sqrdmulh	v5.8h, v31.8h, v26.8h
        sub	v4.8h, v1.8h, v0.8h
        mul	v24.8h, v31.8h, v28.8h
        mul	v23.8h, v8.8h, v29.8h
        mls	v24.8h, v5.8h, v7.h[0]
        sqrdmulh	v28.8h, v4.8h, v25.8h
        mls	v16.8h, v6.8h, v7.h[0]
        mul	v17.8h, v4.8h, v9.8h
        sqrdmulh	v4.8h, v21.8h, v30.8h
        sub	v26.8h, v24.8h, v16.8h
        mls	v17.8h, v28.8h, v7.h[0]
        sqrdmulh	v6.8h, v26.8h, v25.8h
        mul	v8.8h, v26.8h, v9.8h
        mls	v23.8h, v13.8h, v7.h[0]
        mls	v8.8h, v6.8h, v7.h[0]
        sub	x4, x4, #0x2

Lintt_layer4567_start:
        ldr	q20, [x2, #0x40]
        ldr	q28, [x3, #0xb0]
        trn1	v6.4s, v18.4s, v23.4s
        mul	v2.8h, v21.8h, v29.8h
        trn2	v5.4s, v18.4s, v23.4s
        ldr	q12, [x1], #0x10
        mls	v2.8h, v4.8h, v7.h[0]
        add	v13.8h, v24.8h, v16.8h
        ldr	q27, [x2, #0x20]
        trn1	v19.4s, v17.4s, v8.4s
        add	v4.8h, v1.8h, v0.8h
        mul	v23.8h, v28.8h, v29.8h
        ldr	q15, [x2, #0x30]
        trn2	v9.4s, v17.4s, v8.4s
        sqrdmulh	v17.8h, v28.8h, v30.8h
        ldr	q25, [x3, #0xa0]
        trn2	v21.4s, v4.4s, v13.4s
        trn1	v1.4s, v4.4s, v13.4s
        mul	v28.8h, v3.8h, v29.8h
        trn2	v24.2d, v21.2d, v9.2d
        mls	v28.8h, v22.8h, v7.h[0]
        trn2	v14.2d, v1.2d, v19.2d
        mls	v23.8h, v17.8h, v7.h[0]
        add	v10.8h, v14.8h, v24.8h
        sub	v16.8h, v14.8h, v24.8h
        mul	v18.8h, v25.8h, v29.8h
        trn1	v4.4s, v2.4s, v28.4s
        trn2	v17.4s, v2.4s, v28.4s
        sqrdmulh	v31.8h, v25.8h, v30.8h
        trn2	v25.2d, v4.2d, v6.2d
        ldr	q3, [x3, #0x90]
        trn1	v28.2d, v4.2d, v6.2d
        sqrdmulh	v13.8h, v16.8h, v12.h[5]
        trn2	v0.2d, v17.2d, v5.2d
        trn1	v2.2d, v17.2d, v5.2d
        sqdmulh	v22.8h, v10.8h, v7.h[1]
        trn1	v24.2d, v21.2d, v9.2d
        trn1	v5.2d, v1.2d, v19.2d
        mul	v9.8h, v16.8h, v12.h[4]
        mls	v18.8h, v31.8h, v7.h[0]
        sub	v31.8h, v28.8h, v2.8h
        mls	v9.8h, v13.8h, v7.h[0]
        sub	v13.8h, v5.8h, v24.8h
        srshr	v26.8h, v22.8h, #0xb
        mul	v19.8h, v13.8h, v12.h[2]
        sub	v22.8h, v25.8h, v0.8h
        add	v0.8h, v25.8h, v0.8h
        sqrdmulh	v21.8h, v13.8h, v12.h[3]
        add	v14.8h, v5.8h, v24.8h
        sqrdmulh	v6.8h, v31.8h, v15.8h
        mul	v16.8h, v22.8h, v20.8h
        mls	v19.8h, v21.8h, v7.h[0]
        ldr	q21, [x3, #0x80]
        mul	v24.8h, v31.8h, v27.8h
        sqdmulh	v4.8h, v14.8h, v7.h[1]
        sub	v1.8h, v19.8h, v9.8h
        mls	v24.8h, v6.8h, v7.h[0]
        add	v8.8h, v19.8h, v9.8h
        ldr	q6, [x2, #0x50]
        mls	v10.8h, v26.8h, v7.h[0]
        srshr	v13.8h, v4.8h, #0xb
        sqdmulh	v19.8h, v8.8h, v7.h[1]
        sqrdmulh	v4.8h, v21.8h, v30.8h
        mls	v14.8h, v13.8h, v7.h[0]
        srshr	v31.8h, v19.8h, #0xb
        sqrdmulh	v27.8h, v1.8h, v12.h[1]
        mul	v11.8h, v1.8h, v12.h[0]
        add	v1.8h, v28.8h, v2.8h
        sub	v17.8h, v14.8h, v10.8h
        ldr	q28, [x2, #0x10]
        sub	v13.8h, v1.8h, v0.8h
        sqrdmulh	v19.8h, v22.8h, v6.8h
        ldr	q2, [x2], #0x60
        mls	v11.8h, v27.8h, v7.h[0]
        sqrdmulh	v27.8h, v17.8h, v12.h[1]
        mul	v26.8h, v17.8h, v12.h[0]
        str	q11, [x3, #0x30]
        sqrdmulh	v12.8h, v13.8h, v28.8h
        mls	v16.8h, v19.8h, v7.h[0]
        mls	v8.8h, v31.8h, v7.h[0]
        add	v11.8h, v14.8h, v10.8h
        mls	v26.8h, v27.8h, v7.h[0]
        sub	v25.8h, v24.8h, v16.8h
        mul	v17.8h, v13.8h, v2.8h
        str	q11, [x3], #0x40
        stur	q8, [x3, #-0x30]
        sqrdmulh	v10.8h, v25.8h, v28.8h
        mls	v17.8h, v12.8h, v7.h[0]
        mul	v8.8h, v25.8h, v2.8h
        sqrdmulh	v22.8h, v3.8h, v30.8h
        stur	q26, [x3, #-0x20]
        mls	v8.8h, v10.8h, v7.h[0]
        subs	x4, x4, #0x1
        cbnz	x4, Lintt_layer4567_start
        add	v25.8h, v24.8h, v16.8h
        trn1	v12.4s, v17.4s, v8.4s
        mul	v16.8h, v3.8h, v29.8h
        add	v13.8h, v1.8h, v0.8h
        trn2	v20.4s, v18.4s, v23.4s
        ldr	q15, [x2, #0x20]
        trn2	v3.4s, v17.4s, v8.4s
        trn1	v26.4s, v13.4s, v25.4s
        trn2	v13.4s, v13.4s, v25.4s
        mul	v27.8h, v21.8h, v29.8h
        ldr	q0, [x1], #0x10
        trn2	v10.2d, v26.2d, v12.2d
        trn2	v5.2d, v13.2d, v3.2d
        mls	v27.8h, v4.8h, v7.h[0]
        trn1	v19.4s, v18.4s, v23.4s
        sub	v21.8h, v10.8h, v5.8h
        mls	v16.8h, v22.8h, v7.h[0]
        ldr	q2, [x2, #0x30]
        trn1	v17.2d, v26.2d, v12.2d
        mul	v6.8h, v21.8h, v0.h[4]
        trn1	v13.2d, v13.2d, v3.2d
        add	v10.8h, v10.8h, v5.8h
        ldr	q9, [x2, #0x40]
        sqrdmulh	v22.8h, v21.8h, v0.h[5]
        add	v18.8h, v17.8h, v13.8h
        trn1	v31.4s, v27.4s, v16.4s
        sub	v13.8h, v17.8h, v13.8h
        sqdmulh	v12.8h, v18.8h, v7.h[1]
        trn2	v8.4s, v27.4s, v16.4s
        trn1	v14.2d, v31.2d, v19.2d
        sqrdmulh	v25.8h, v13.8h, v0.h[3]
        trn1	v3.2d, v8.2d, v20.2d
        mul	v1.8h, v13.8h, v0.h[2]
        trn2	v4.2d, v31.2d, v19.2d
        sub	v13.8h, v14.8h, v3.8h
        sqdmulh	v26.8h, v10.8h, v7.h[1]
        trn2	v8.2d, v8.2d, v20.2d
        ldr	q5, [x2, #0x50]
        sqrdmulh	v31.8h, v13.8h, v2.8h
        sub	v19.8h, v4.8h, v8.8h
        mul	v21.8h, v13.8h, v15.8h
        sqrdmulh	v5.8h, v19.8h, v5.8h
        mul	v13.8h, v19.8h, v9.8h
        mls	v21.8h, v31.8h, v7.h[0]
        add	v9.8h, v14.8h, v3.8h
        srshr	v3.8h, v26.8h, #0xb
        mls	v13.8h, v5.8h, v7.h[0]
        mls	v6.8h, v22.8h, v7.h[0]
        add	v14.8h, v4.8h, v8.8h
        ldr	q5, [x2], #0x60
        mls	v10.8h, v3.8h, v7.h[0]
        ldur	q4, [x2, #-0x50]
        sub	v3.8h, v21.8h, v13.8h
        mls	v1.8h, v25.8h, v7.h[0]
        srshr	v26.8h, v12.8h, #0xb
        sub	v8.8h, v9.8h, v14.8h
        mul	v25.8h, v3.8h, v5.8h
        sqrdmulh	v31.8h, v8.8h, v4.8h
        add	v27.8h, v21.8h, v13.8h
        sqrdmulh	v11.8h, v3.8h, v4.8h
        mls	v18.8h, v26.8h, v7.h[0]
        sub	v15.8h, v1.8h, v6.8h
        sqrdmulh	v22.8h, v15.8h, v0.h[1]
        mls	v25.8h, v11.8h, v7.h[0]
        mul	v26.8h, v8.8h, v5.8h
        add	v2.8h, v1.8h, v6.8h
        mls	v26.8h, v31.8h, v7.h[0]
        add	v20.8h, v9.8h, v14.8h
        sub	v5.8h, v18.8h, v10.8h
        trn2	v4.4s, v20.4s, v27.4s
        mul	v6.8h, v15.8h, v0.h[0]
        add	v14.8h, v18.8h, v10.8h
        trn1	v3.4s, v20.4s, v27.4s
        sqrdmulh	v9.8h, v5.8h, v0.h[1]
        trn1	v31.4s, v26.4s, v25.4s
        sqdmulh	v12.8h, v2.8h, v7.h[1]
        trn2	v27.4s, v26.4s, v25.4s
        trn2	v8.2d, v3.2d, v31.2d
        trn2	v10.2d, v4.2d, v27.2d
        mls	v6.8h, v22.8h, v7.h[0]
        trn1	v11.2d, v4.2d, v27.2d
        ldr	q4, [x1], #0x10
        add	v13.8h, v8.8h, v10.8h
        mul	v1.8h, v5.8h, v0.h[0]
        trn1	v21.2d, v3.2d, v31.2d
        sqdmulh	v20.8h, v13.8h, v7.h[1]
        sub	v5.8h, v8.8h, v10.8h
        add	v25.8h, v21.8h, v11.8h
        mul	v31.8h, v5.8h, v4.h[4]
        sub	v10.8h, v21.8h, v11.8h
        sqdmulh	v27.8h, v25.8h, v7.h[1]
        sqrdmulh	v8.8h, v5.8h, v4.h[5]
        mul	v11.8h, v10.8h, v4.h[2]
        srshr	v0.8h, v20.8h, #0xb
        srshr	v5.8h, v27.8h, #0xb
        sqrdmulh	v26.8h, v10.8h, v4.h[3]
        mls	v13.8h, v0.8h, v7.h[0]
        mls	v25.8h, v5.8h, v7.h[0]
        mls	v11.8h, v26.8h, v7.h[0]
        srshr	v27.8h, v12.8h, #0xb
        mls	v31.8h, v8.8h, v7.h[0]
        sub	v0.8h, v25.8h, v13.8h
        mls	v1.8h, v9.8h, v7.h[0]
        sqrdmulh	v26.8h, v0.8h, v4.h[1]
        sub	v8.8h, v11.8h, v31.8h
        add	v12.8h, v11.8h, v31.8h
        mul	v20.8h, v0.8h, v4.h[0]
        sqdmulh	v11.8h, v12.8h, v7.h[1]
        sqrdmulh	v31.8h, v8.8h, v4.h[1]
        mls	v20.8h, v26.8h, v7.h[0]
        str	q6, [x3, #0x30]
        add	v6.8h, v25.8h, v13.8h
        srshr	v13.8h, v11.8h, #0xb
        mul	v4.8h, v8.8h, v4.h[0]
        mls	v4.8h, v31.8h, v7.h[0]
        str	q20, [x3, #0x60]
        mls	v12.8h, v13.8h, v7.h[0]
        mls	v2.8h, v27.8h, v7.h[0]
        str	q14, [x3], #0x40
        str	q12, [x3, #0x10]
        str	q6, [x3], #0x40
        stur	q1, [x3, #-0x60]
        stur	q2, [x3, #-0x70]
        stur	q4, [x3, #-0x10]
        mov	x4, #0x4                // =4
        ldr	q0, [x1], #0x20
        ldur	q1, [x1, #-0x10]
        ldr	q29, [x0, #0xc0]
        ldr	q4, [x0, #0x80]
        ldr	q28, [x0, #0x40]
        ldr	q16, [x0]
        ldr	q13, [x0, #0x100]
        ldr	q12, [x0, #0x1c0]
        ldr	q18, [x0, #0x140]
        ldr	q9, [x0, #0x180]
        sub	v21.8h, v4.8h, v29.8h
        add	v30.8h, v4.8h, v29.8h
        sub	v26.8h, v16.8h, v28.8h
        add	v14.8h, v16.8h, v28.8h
        ldr	q25, [x0, #0x10]
        sqrdmulh	v8.8h, v21.8h, v1.h[1]
        add	v24.8h, v13.8h, v18.8h
        ldr	q17, [x0, #0x50]
        sub	v4.8h, v13.8h, v18.8h
        sqrdmulh	v22.8h, v26.8h, v0.h[7]
        add	v19.8h, v9.8h, v12.8h
        ldr	q5, [x0, #0x90]
        sub	v13.8h, v9.8h, v12.8h
        mul	v12.8h, v21.8h, v1.h[0]
        sub	v29.8h, v14.8h, v30.8h
        ldr	q27, [x0, #0xd0]
        mul	v16.8h, v26.8h, v0.h[6]
        sub	v18.8h, v24.8h, v19.8h
        ldr	q6, [x0, #0x110]
        ldr	q21, [x0, #0x150]
        add	v26.8h, v24.8h, v19.8h
        sqrdmulh	v23.8h, v18.8h, v0.h[5]
        add	v3.8h, v14.8h, v30.8h
        ldr	q19, [x0, #0x190]
        sqrdmulh	v28.8h, v29.8h, v0.h[3]
        add	v10.8h, v25.8h, v17.8h
        add	v31.8h, v5.8h, v27.8h
        ldr	q24, [x0, #0x1d0]
        mul	v14.8h, v18.8h, v0.h[4]
        sub	v15.8h, v3.8h, v26.8h
        sub	v30.8h, v10.8h, v31.8h
        mul	v29.8h, v29.8h, v0.h[2]
        sub	v2.8h, v6.8h, v21.8h
        add	v26.8h, v3.8h, v26.8h
        mls	v29.8h, v28.8h, v7.h[0]
        sub	v9.8h, v19.8h, v24.8h
        sub	v11.8h, v25.8h, v17.8h
        str	q26, [x0], #0x10
        mls	v16.8h, v22.8h, v7.h[0]
        mls	v12.8h, v8.8h, v7.h[0]
        mls	v14.8h, v23.8h, v7.h[0]
        sqrdmulh	v26.8h, v13.8h, v1.h[5]
        sub	v25.8h, v16.8h, v12.8h
        add	v20.8h, v16.8h, v12.8h
        mul	v18.8h, v4.8h, v1.h[2]
        sub	v22.8h, v29.8h, v14.8h
        sqrdmulh	v4.8h, v4.8h, v1.h[3]
        add	v12.8h, v29.8h, v14.8h
        str	q12, [x0, #0x70]
        sqrdmulh	v3.8h, v25.8h, v0.h[3]
        sqrdmulh	v12.8h, v22.8h, v0.h[1]
        mul	v29.8h, v13.8h, v1.h[4]
        mul	v23.8h, v22.8h, v0.h[0]
        mul	v14.8h, v25.8h, v0.h[2]
        mls	v29.8h, v26.8h, v7.h[0]
        mls	v23.8h, v12.8h, v7.h[0]
        mul	v16.8h, v30.8h, v0.h[2]
        mls	v14.8h, v3.8h, v7.h[0]
        sqrdmulh	v22.8h, v15.8h, v0.h[1]
        sqrdmulh	v30.8h, v30.8h, v0.h[3]
        mul	v8.8h, v15.8h, v0.h[0]
        mls	v18.8h, v4.8h, v7.h[0]
        sqrdmulh	v12.8h, v2.8h, v1.h[3]
        sub	x4, x4, #0x2

Lintt_layer123_start:
        sub	v3.8h, v18.8h, v29.8h
        sqrdmulh	v28.8h, v11.8h, v0.h[7]
        add	v13.8h, v18.8h, v29.8h
        str	q23, [x0, #0x170]
        ldr	q15, [x0, #0x50]
        mul	v29.8h, v9.8h, v1.h[4]
        add	v10.8h, v10.8h, v31.8h
        mls	v8.8h, v22.8h, v7.h[0]
        sub	v17.8h, v20.8h, v13.8h
        add	v31.8h, v19.8h, v24.8h
        mul	v18.8h, v2.8h, v1.h[2]
        ldr	q24, [x0, #0x1d0]
        sub	v5.8h, v5.8h, v27.8h
        mls	v16.8h, v30.8h, v7.h[0]
        str	q8, [x0, #0xf0]
        add	v8.8h, v6.8h, v21.8h
        add	v6.8h, v20.8h, v13.8h
        sqrdmulh	v13.8h, v9.8h, v1.h[5]
        ldr	q4, [x0, #0x10]
        sub	v20.8h, v8.8h, v31.8h
        mul	v26.8h, v5.8h, v1.h[0]
        ldr	q19, [x0, #0x190]
        add	v31.8h, v8.8h, v31.8h
        ldr	q21, [x0, #0x150]
        sqrdmulh	v22.8h, v20.8h, v0.h[5]
        str	q6, [x0, #0x30]
        add	v25.8h, v10.8h, v31.8h
        ldr	q6, [x0, #0x110]
        mul	v23.8h, v20.8h, v0.h[4]
        str	q25, [x0], #0x10
        mls	v18.8h, v12.8h, v7.h[0]
        sub	v2.8h, v6.8h, v21.8h
        mls	v23.8h, v22.8h, v7.h[0]
        mul	v8.8h, v11.8h, v0.h[6]
        mls	v8.8h, v28.8h, v7.h[0]
        add	v22.8h, v16.8h, v23.8h
        sub	v11.8h, v16.8h, v23.8h
        sqrdmulh	v16.8h, v3.8h, v0.h[5]
        str	q22, [x0, #0x70]
        sqrdmulh	v27.8h, v5.8h, v1.h[1]
        mls	v29.8h, v13.8h, v7.h[0]
        mul	v23.8h, v3.8h, v0.h[4]
        ldr	q5, [x0, #0x80]
        sub	v28.8h, v10.8h, v31.8h
        mls	v26.8h, v27.8h, v7.h[0]
        sqrdmulh	v22.8h, v28.8h, v0.h[1]
        ldr	q27, [x0, #0xc0]
        mls	v23.8h, v16.8h, v7.h[0]
        sub	v10.8h, v8.8h, v26.8h
        add	v20.8h, v8.8h, v26.8h
        mul	v26.8h, v17.8h, v0.h[0]
        sqrdmulh	v9.8h, v10.8h, v0.h[3]
        add	v31.8h, v5.8h, v27.8h
        sqrdmulh	v30.8h, v17.8h, v0.h[1]
        sub	v16.8h, v14.8h, v23.8h
        add	v17.8h, v14.8h, v23.8h
        mul	v14.8h, v10.8h, v0.h[2]
        str	q17, [x0, #0xa0]
        mls	v14.8h, v9.8h, v7.h[0]
        sqrdmulh	v9.8h, v16.8h, v0.h[1]
        sqrdmulh	v10.8h, v11.8h, v0.h[1]
        mls	v26.8h, v30.8h, v7.h[0]
        sqrdmulh	v12.8h, v2.8h, v1.h[3]
        mul	v23.8h, v11.8h, v0.h[0]
        sub	v11.8h, v4.8h, v15.8h
        str	q26, [x0, #0x120]
        mls	v23.8h, v10.8h, v7.h[0]
        add	v10.8h, v4.8h, v15.8h
        mul	v26.8h, v16.8h, v0.h[0]
        sub	v30.8h, v10.8h, v31.8h
        mul	v16.8h, v30.8h, v0.h[2]
        mls	v26.8h, v9.8h, v7.h[0]
        sub	v9.8h, v19.8h, v24.8h
        mul	v8.8h, v28.8h, v0.h[0]
        sqrdmulh	v30.8h, v30.8h, v0.h[3]
        str	q26, [x0, #0x1a0]
        subs	x4, x4, #0x1
        cbnz	x4, Lintt_layer123_start
        mls	v16.8h, v30.8h, v7.h[0]
        add	v15.8h, v19.8h, v24.8h
        str	q23, [x0, #0x170]
        add	v13.8h, v6.8h, v21.8h
        sqrdmulh	v25.8h, v11.8h, v0.h[7]
        add	v3.8h, v10.8h, v31.8h
        sub	v21.8h, v13.8h, v15.8h
        mul	v24.8h, v11.8h, v0.h[6]
        sub	v17.8h, v5.8h, v27.8h
        sub	v28.8h, v18.8h, v29.8h
        mul	v19.8h, v9.8h, v1.h[4]
        add	v23.8h, v13.8h, v15.8h
        add	v27.8h, v18.8h, v29.8h
        mul	v6.8h, v2.8h, v1.h[2]
        mls	v6.8h, v12.8h, v7.h[0]
        mls	v24.8h, v25.8h, v7.h[0]
        mls	v8.8h, v22.8h, v7.h[0]
        sqrdmulh	v31.8h, v21.8h, v0.h[5]
        add	v22.8h, v3.8h, v23.8h
        sqrdmulh	v4.8h, v17.8h, v1.h[1]
        str	q8, [x0, #0xf0]
        str	q22, [x0], #0x10
        mul	v8.8h, v17.8h, v1.h[0]
        sqrdmulh	v26.8h, v9.8h, v1.h[5]
        mls	v8.8h, v4.8h, v7.h[0]
        sub	v4.8h, v20.8h, v27.8h
        sub	v10.8h, v3.8h, v23.8h
        sqrdmulh	v30.8h, v4.8h, v0.h[1]
        sqrdmulh	v11.8h, v10.8h, v0.h[1]
        sub	v15.8h, v24.8h, v8.8h
        mls	v19.8h, v26.8h, v7.h[0]
        sqrdmulh	v26.8h, v28.8h, v0.h[5]
        mul	v18.8h, v4.8h, v0.h[0]
        add	v12.8h, v6.8h, v19.8h
        sub	v3.8h, v6.8h, v19.8h
        mls	v18.8h, v30.8h, v7.h[0]
        mul	v30.8h, v21.8h, v0.h[4]
        mls	v30.8h, v31.8h, v7.h[0]
        str	q18, [x0, #0x120]
        mul	v21.8h, v28.8h, v0.h[4]
        sqrdmulh	v2.8h, v15.8h, v0.h[3]
        add	v19.8h, v16.8h, v30.8h
        mls	v21.8h, v26.8h, v7.h[0]
        sub	v5.8h, v16.8h, v30.8h
        mul	v23.8h, v10.8h, v0.h[0]
        sqrdmulh	v10.8h, v5.8h, v0.h[1]
        add	v16.8h, v20.8h, v27.8h
        add	v20.8h, v24.8h, v8.8h
        mul	v6.8h, v5.8h, v0.h[0]
        sub	v5.8h, v14.8h, v21.8h
        str	q16, [x0, #0x20]
        sub	v26.8h, v20.8h, v12.8h
        add	v8.8h, v20.8h, v12.8h
        sqrdmulh	v12.8h, v3.8h, v0.h[5]
        str	q19, [x0, #0x70]
        str	q8, [x0, #0x30]
        sqrdmulh	v9.8h, v5.8h, v0.h[1]
        add	v4.8h, v14.8h, v21.8h
        mls	v6.8h, v10.8h, v7.h[0]
        str	q4, [x0, #0xa0]
        mul	v10.8h, v3.8h, v0.h[4]
        mls	v10.8h, v12.8h, v7.h[0]
        str	q6, [x0, #0x170]
        mul	v6.8h, v15.8h, v0.h[2]
        mls	v6.8h, v2.8h, v7.h[0]
        sqrdmulh	v14.8h, v26.8h, v0.h[1]
        mls	v23.8h, v11.8h, v7.h[0]
        sub	v13.8h, v6.8h, v10.8h
        mul	v15.8h, v26.8h, v0.h[0]
        add	v31.8h, v6.8h, v10.8h
        mls	v15.8h, v14.8h, v7.h[0]
        str	q31, [x0, #0xb0]
        sqrdmulh	v8.8h, v13.8h, v0.h[1]
        str	q23, [x0, #0xf0]
        mul	v11.8h, v13.8h, v0.h[0]
        mul	v21.8h, v5.8h, v0.h[0]
        str	q15, [x0, #0x130]
        mls	v11.8h, v8.8h, v7.h[0]
        mls	v21.8h, v9.8h, v7.h[0]
        str	q11, [x0, #0x1b0]
        str	q21, [x0, #0x1a0]
        ldp	d8, d9, [sp]
        .cfi_restore d8
        .cfi_restore d9
        ldp	d10, d11, [sp, #0x10]
        .cfi_restore d10
        .cfi_restore d11
        ldp	d12, d13, [sp, #0x20]
        .cfi_restore d12
        .cfi_restore d13
        ldp	d14, d15, [sp, #0x30]
        .cfi_restore d14
        .cfi_restore d15
        add	sp, sp, #0x40
        .cfi_adjust_cfa_offset -0x40
        ret
        .cfi_endproc

#endif /* MLK_ARITH_BACKEND_AARCH64 && !MLK_CONFIG_MULTILEVEL_NO_SHARED */
