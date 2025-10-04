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


/*
 * WARNING: This file is auto-derived from the mlkem-native source file
 *   dev/aarch64_opt/src/intt.S using scripts/simpasm. Do not modify it directly.
 */


.text
.balign 4
#ifdef __APPLE__
.global _PQCP_MLKEM_NATIVE_MLKEM768_intt_asm
_PQCP_MLKEM_NATIVE_MLKEM768_intt_asm:
#else
.global PQCP_MLKEM_NATIVE_MLKEM768_intt_asm
PQCP_MLKEM_NATIVE_MLKEM768_intt_asm:
#endif

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

Lintt_scale_start:
        ldr	q8, [x3]
        ldr	q9, [x3, #0x10]
        ldr	q10, [x3, #0x20]
        ldr	q11, [x3, #0x30]
        sqrdmulh	v27.8h, v8.8h, v30.8h
        mul	v8.8h, v8.8h, v29.8h
        mls	v8.8h, v27.8h, v7.h[0]
        sqrdmulh	v27.8h, v9.8h, v30.8h
        mul	v9.8h, v9.8h, v29.8h
        mls	v9.8h, v27.8h, v7.h[0]
        sqrdmulh	v27.8h, v10.8h, v30.8h
        mul	v10.8h, v10.8h, v29.8h
        mls	v10.8h, v27.8h, v7.h[0]
        sqrdmulh	v27.8h, v11.8h, v30.8h
        mul	v11.8h, v11.8h, v29.8h
        mls	v11.8h, v27.8h, v7.h[0]
        str	q8, [x3], #0x40
        stur	q9, [x3, #-0x30]
        stur	q10, [x3, #-0x20]
        stur	q11, [x3, #-0x10]
        subs	x4, x4, #0x1
        cbnz	x4, Lintt_scale_start
        mov	x3, x0
        mov	x4, #0x8                // =8
        ldr	q21, [x3]
        ldr	q30, [x3, #0x10]
        ldr	q13, [x3, #0x30]
        ldr	q12, [x3, #0x20]
        trn1	v27.4s, v21.4s, v30.4s
        trn2	v21.4s, v21.4s, v30.4s
        trn2	v10.4s, v12.4s, v13.4s
        trn1	v22.4s, v12.4s, v13.4s
        ldr	q3, [x2, #0x50]
        trn2	v5.2d, v27.2d, v22.2d
        trn2	v12.2d, v21.2d, v10.2d
        trn1	v9.2d, v21.2d, v10.2d
        trn1	v30.2d, v27.2d, v22.2d
        sub	v21.8h, v5.8h, v12.8h
        ldr	q13, [x2, #0x30]
        ldr	q15, [x2, #0x20]
        sqrdmulh	v31.8h, v21.8h, v3.8h
        sub	v10.8h, v30.8h, v9.8h
        ldr	q6, [x2, #0xa0]
        sqrdmulh	v13.8h, v10.8h, v13.8h
        ldr	q3, [x2, #0x40]
        add	v30.8h, v30.8h, v9.8h
        mul	v28.8h, v10.8h, v15.8h
        ldr	q25, [x3, #0x50]
        ldr	q24, [x2], #0x60
        add	v10.8h, v5.8h, v12.8h
        mul	v12.8h, v21.8h, v3.8h
        ldr	q15, [x3, #0x40]
        add	v9.8h, v30.8h, v10.8h
        ldr	q3, [x3, #0x60]
        mls	v12.8h, v31.8h, v7.h[0]
        ldr	q31, [x3, #0x70]
        sub	v21.8h, v30.8h, v10.8h
        mls	v28.8h, v13.8h, v7.h[0]
        trn2	v5.4s, v15.4s, v25.4s
        ldur	q13, [x2, #-0x50]
        trn1	v15.4s, v15.4s, v25.4s
        trn1	v26.4s, v3.4s, v31.4s
        mul	v11.8h, v21.8h, v24.8h
        trn2	v19.2d, v15.2d, v26.2d
        ldr	q27, [x2, #0x50]
        sqrdmulh	v30.8h, v21.8h, v13.8h
        sub	v21.8h, v28.8h, v12.8h
        sqrdmulh	v25.8h, v21.8h, v13.8h
        add	v16.8h, v28.8h, v12.8h
        trn2	v13.4s, v3.4s, v31.4s
        mul	v4.8h, v21.8h, v24.8h
        trn1	v3.2d, v5.2d, v13.2d
        mls	v11.8h, v30.8h, v7.h[0]
        trn2	v28.2d, v5.2d, v13.2d
        trn1	v21.2d, v15.2d, v26.2d
        ldr	q10, [x2, #0x30]
        mls	v4.8h, v25.8h, v7.h[0]
        sub	v5.8h, v19.8h, v28.8h
        sub	v13.8h, v21.8h, v3.8h
        sqrdmulh	v31.8h, v5.8h, v27.8h
        trn1	v1.4s, v9.4s, v16.4s
        trn2	v9.4s, v9.4s, v16.4s
        ldr	q20, [x2, #0x20]
        sqrdmulh	v18.8h, v13.8h, v10.8h
        add	v30.8h, v21.8h, v3.8h
        trn1	v25.4s, v11.4s, v4.4s
        trn2	v21.4s, v11.4s, v4.4s
        trn2	v10.2d, v1.2d, v25.2d
        ldr	q12, [x1], #0x10
        mul	v15.8h, v13.8h, v20.8h
        trn2	v13.2d, v9.2d, v21.2d
        add	v23.8h, v10.8h, v13.8h
        sub	v10.8h, v10.8h, v13.8h
        trn1	v9.2d, v9.2d, v21.2d
        sqrdmulh	v13.8h, v10.8h, v12.h[5]
        sqdmulh	v3.8h, v23.8h, v7.h[1]
        trn1	v21.2d, v1.2d, v25.2d
        mul	v29.8h, v10.8h, v12.h[4]
        add	v4.8h, v21.8h, v9.8h
        mls	v29.8h, v13.8h, v7.h[0]
        sub	v10.8h, v21.8h, v9.8h
        sqrdmulh	v21.8h, v10.8h, v12.h[3]
        sqdmulh	v13.8h, v4.8h, v7.h[1]
        mul	v17.8h, v10.8h, v12.h[2]
        srshr	v10.8h, v3.8h, #0xb
        mls	v17.8h, v21.8h, v7.h[0]
        srshr	v13.8h, v13.8h, #0xb
        mls	v23.8h, v10.8h, v7.h[0]
        mls	v4.8h, v13.8h, v7.h[0]
        add	v11.8h, v17.8h, v29.8h
        sqdmulh	v13.8h, v11.8h, v7.h[1]
        sub	v10.8h, v17.8h, v29.8h
        sub	x4, x4, #0x2

Lintt_layer4567_start:
        mls	v15.8h, v18.8h, v7.h[0]
        ldr	q26, [x3, #0x90]
        mul	v14.8h, v10.8h, v12.h[0]
        ldr	q9, [x2], #0x60
        ldr	q16, [x3, #0x80]
        srshr	v18.8h, v13.8h, #0xb
        sqrdmulh	v21.8h, v10.8h, v12.h[1]
        add	v10.8h, v19.8h, v28.8h
        mul	v5.8h, v5.8h, v6.8h
        ldr	q25, [x2, #0x50]
        sub	v13.8h, v4.8h, v23.8h
        mls	v11.8h, v18.8h, v7.h[0]
        add	v6.8h, v30.8h, v10.8h
        sub	v10.8h, v30.8h, v10.8h
        ldur	q30, [x2, #-0x50]
        mls	v5.8h, v31.8h, v7.h[0]
        trn2	v28.4s, v16.4s, v26.4s
        mul	v18.8h, v10.8h, v9.8h
        ldr	q27, [x3, #0xb0]
        sqrdmulh	v3.8h, v10.8h, v30.8h
        add	v10.8h, v4.8h, v23.8h
        sub	v17.8h, v15.8h, v5.8h
        ldr	q20, [x3, #0xa0]
        add	v31.8h, v15.8h, v5.8h
        sqrdmulh	v4.8h, v13.8h, v12.h[1]
        trn1	v15.4s, v16.4s, v26.4s
        str	q10, [x3], #0x40
        sqrdmulh	v10.8h, v17.8h, v30.8h
        trn1	v30.4s, v6.4s, v31.4s
        stur	q11, [x3, #-0x30]
        trn2	v5.4s, v20.4s, v27.4s
        mul	v1.8h, v17.8h, v9.8h
        trn1	v9.4s, v20.4s, v27.4s
        ldr	q20, [x2, #0x20]
        mls	v18.8h, v3.8h, v7.h[0]
        trn1	v27.2d, v28.2d, v5.2d
        trn2	v19.2d, v15.2d, v9.2d
        mls	v1.8h, v10.8h, v7.h[0]
        trn1	v8.2d, v15.2d, v9.2d
        trn2	v28.2d, v28.2d, v5.2d
        ldr	q15, [x2, #0x30]
        mul	v0.8h, v13.8h, v12.h[0]
        sub	v9.8h, v8.8h, v27.8h
        sub	v5.8h, v19.8h, v28.8h
        ldr	q12, [x1], #0x10
        mls	v0.8h, v4.8h, v7.h[0]
        trn2	v6.4s, v6.4s, v31.4s
        trn1	v3.4s, v18.4s, v1.4s
        mls	v14.8h, v21.8h, v7.h[0]
        trn2	v21.4s, v18.4s, v1.4s
        trn2	v10.2d, v30.2d, v3.2d
        sqrdmulh	v31.8h, v5.8h, v25.8h
        trn2	v13.2d, v6.2d, v21.2d
        trn1	v16.2d, v6.2d, v21.2d
        stur	q0, [x3, #-0x20]
        sqrdmulh	v18.8h, v9.8h, v15.8h
        add	v23.8h, v10.8h, v13.8h
        trn1	v3.2d, v30.2d, v3.2d
        stur	q14, [x3, #-0x10]
        sub	v10.8h, v10.8h, v13.8h
        sqdmulh	v13.8h, v23.8h, v7.h[1]
        add	v4.8h, v3.8h, v16.8h
        add	v30.8h, v8.8h, v27.8h
        sqrdmulh	v21.8h, v10.8h, v12.h[5]
        mul	v6.8h, v10.8h, v12.h[4]
        sub	v10.8h, v3.8h, v16.8h
        sqrdmulh	v3.8h, v10.8h, v12.h[3]
        mul	v2.8h, v10.8h, v12.h[2]
        srshr	v13.8h, v13.8h, #0xb
        sqdmulh	v10.8h, v4.8h, v7.h[1]
        mls	v2.8h, v3.8h, v7.h[0]
        mls	v6.8h, v21.8h, v7.h[0]
        mls	v23.8h, v13.8h, v7.h[0]
        srshr	v13.8h, v10.8h, #0xb
        mul	v15.8h, v9.8h, v20.8h
        add	v11.8h, v2.8h, v6.8h
        mls	v4.8h, v13.8h, v7.h[0]
        sub	v10.8h, v2.8h, v6.8h
        sqdmulh	v13.8h, v11.8h, v7.h[1]
        ldr	q6, [x2, #0x40]
        subs	x4, x4, #0x1
        cbnz	x4, Lintt_layer4567_start
        mls	v15.8h, v18.8h, v7.h[0]
        add	v20.8h, v19.8h, v28.8h
        ldr	q24, [x2], #0x60
        mul	v5.8h, v5.8h, v6.8h
        sub	v21.8h, v30.8h, v20.8h
        ldur	q22, [x2, #-0x50]
        mls	v5.8h, v31.8h, v7.h[0]
        mul	v28.8h, v21.8h, v24.8h
        sqrdmulh	v6.8h, v21.8h, v22.8h
        sub	v3.8h, v15.8h, v5.8h
        sqrdmulh	v25.8h, v10.8h, v12.h[1]
        sqrdmulh	v21.8h, v3.8h, v22.8h
        mul	v19.8h, v3.8h, v24.8h
        mls	v28.8h, v6.8h, v7.h[0]
        sub	v31.8h, v4.8h, v23.8h
        mls	v19.8h, v21.8h, v7.h[0]
        add	v3.8h, v30.8h, v20.8h
        add	v21.8h, v15.8h, v5.8h
        srshr	v15.8h, v13.8h, #0xb
        sqrdmulh	v20.8h, v31.8h, v12.h[1]
        trn2	v6.4s, v3.4s, v21.4s
        trn1	v5.4s, v3.4s, v21.4s
        mul	v18.8h, v10.8h, v12.h[0]
        trn1	v13.4s, v28.4s, v19.4s
        trn2	v3.4s, v28.4s, v19.4s
        mul	v1.8h, v31.8h, v12.h[0]
        ldr	q9, [x1], #0x10
        trn2	v21.2d, v5.2d, v13.2d
        mls	v11.8h, v15.8h, v7.h[0]
        trn2	v10.2d, v6.2d, v3.2d
        trn1	v13.2d, v5.2d, v13.2d
        mls	v18.8h, v25.8h, v7.h[0]
        sub	v31.8h, v21.8h, v10.8h
        trn1	v3.2d, v6.2d, v3.2d
        add	v25.8h, v21.8h, v10.8h
        sqrdmulh	v10.8h, v31.8h, v9.h[5]
        sub	v21.8h, v13.8h, v3.8h
        sqdmulh	v30.8h, v25.8h, v7.h[1]
        add	v5.8h, v13.8h, v3.8h
        sqrdmulh	v15.8h, v21.8h, v9.h[3]
        sqdmulh	v13.8h, v5.8h, v7.h[1]
        mul	v3.8h, v31.8h, v9.h[4]
        mls	v3.8h, v10.8h, v7.h[0]
        srshr	v10.8h, v30.8h, #0xb
        srshr	v13.8h, v13.8h, #0xb
        mul	v31.8h, v21.8h, v9.h[2]
        mls	v31.8h, v15.8h, v7.h[0]
        mls	v5.8h, v13.8h, v7.h[0]
        mls	v25.8h, v10.8h, v7.h[0]
        add	v30.8h, v31.8h, v3.8h
        mls	v1.8h, v20.8h, v7.h[0]
        sub	v3.8h, v31.8h, v3.8h
        sqdmulh	v10.8h, v30.8h, v7.h[1]
        sub	v13.8h, v5.8h, v25.8h
        sqrdmulh	v21.8h, v3.8h, v9.h[1]
        mul	v12.8h, v3.8h, v9.h[0]
        srshr	v6.8h, v10.8h, #0xb
        sqrdmulh	v10.8h, v13.8h, v9.h[1]
        mul	v13.8h, v13.8h, v9.h[0]
        mls	v30.8h, v6.8h, v7.h[0]
        mls	v13.8h, v10.8h, v7.h[0]
        str	q1, [x3, #0x20]
        mls	v12.8h, v21.8h, v7.h[0]
        add	v21.8h, v4.8h, v23.8h
        add	v10.8h, v5.8h, v25.8h
        str	q21, [x3], #0x40
        str	q30, [x3, #0x10]
        str	q13, [x3, #0x20]
        str	q10, [x3], #0x40
        stur	q11, [x3, #-0x70]
        stur	q12, [x3, #-0x10]
        stur	q18, [x3, #-0x50]
        mov	x4, #0x4                // =4
        ldr	q0, [x1], #0x20
        ldur	q1, [x1, #-0x10]
        ldr	q29, [x0, #0x140]
        ldr	q19, [x0, #0x100]
        ldr	q9, [x0, #0x180]
        ldr	q28, [x0, #0x1c0]
        ldr	q11, [x0, #0xc0]
        ldr	q31, [x0, #0x80]
        ldr	q3, [x0, #0xd0]
        ldr	q15, [x0, #0x40]
        add	v20.8h, v19.8h, v29.8h
        sub	v18.8h, v19.8h, v29.8h
        add	v27.8h, v9.8h, v28.8h
        sub	v17.8h, v9.8h, v28.8h
        sqrdmulh	v16.8h, v18.8h, v1.h[3]
        sub	v26.8h, v31.8h, v11.8h
        add	v31.8h, v31.8h, v11.8h
        ldr	q24, [x0, #0x1d0]
        sqrdmulh	v23.8h, v17.8h, v1.h[5]
        ldr	q19, [x0, #0x190]
        add	v9.8h, v20.8h, v27.8h
        sub	v14.8h, v20.8h, v27.8h
        mul	v22.8h, v18.8h, v1.h[2]
        mul	v29.8h, v17.8h, v1.h[4]
        mls	v22.8h, v16.8h, v7.h[0]
        mls	v29.8h, v23.8h, v7.h[0]
        mul	v16.8h, v26.8h, v1.h[0]
        sqrdmulh	v28.8h, v26.8h, v1.h[1]
        sub	v8.8h, v22.8h, v29.8h
        sqrdmulh	v11.8h, v8.8h, v0.h[5]
        mul	v23.8h, v8.8h, v0.h[4]
        mls	v23.8h, v11.8h, v7.h[0]
        sub	x4, x4, #0x2

Lintt_layer123_start:
        sub	v20.8h, v19.8h, v24.8h
        sqrdmulh	v27.8h, v14.8h, v0.h[5]
        ldr	q8, [x0]
        add	v21.8h, v22.8h, v29.8h
        mul	v29.8h, v20.8h, v1.h[4]
        ldr	q13, [x0, #0x110]
        sqrdmulh	v10.8h, v20.8h, v1.h[5]
        ldr	q2, [x0, #0x150]
        mul	v11.8h, v14.8h, v0.h[4]
        add	v20.8h, v8.8h, v15.8h
        mls	v11.8h, v27.8h, v7.h[0]
        sub	v4.8h, v13.8h, v2.8h
        add	v24.8h, v19.8h, v24.8h
        sub	v6.8h, v8.8h, v15.8h
        sqrdmulh	v14.8h, v4.8h, v1.h[3]
        add	v30.8h, v13.8h, v2.8h
        ldr	q19, [x0, #0x1a0]
        mul	v22.8h, v4.8h, v1.h[2]
        ldr	q15, [x0, #0x50]
        sqrdmulh	v17.8h, v6.8h, v0.h[7]
        add	v13.8h, v20.8h, v31.8h
        ldr	q4, [x0, #0x90]
        mls	v22.8h, v14.8h, v7.h[0]
        add	v25.8h, v13.8h, v9.8h
        sub	v8.8h, v13.8h, v9.8h
        mls	v29.8h, v10.8h, v7.h[0]
        sub	v14.8h, v30.8h, v24.8h
        add	v9.8h, v30.8h, v24.8h
        str	q25, [x0], #0x10
        mls	v16.8h, v28.8h, v7.h[0]
        ldr	q24, [x0, #0x1d0]
        sub	v13.8h, v4.8h, v3.8h
        mul	v26.8h, v6.8h, v0.h[6]
        mls	v26.8h, v17.8h, v7.h[0]
        sub	v27.8h, v22.8h, v29.8h
        sqrdmulh	v28.8h, v13.8h, v1.h[1]
        sqrdmulh	v10.8h, v27.8h, v0.h[5]
        add	v30.8h, v26.8h, v16.8h
        mul	v18.8h, v8.8h, v0.h[0]
        sub	v5.8h, v30.8h, v21.8h
        add	v12.8h, v30.8h, v21.8h
        sqrdmulh	v21.8h, v8.8h, v0.h[1]
        sub	v8.8h, v26.8h, v16.8h
        mul	v16.8h, v13.8h, v1.h[0]
        sub	v13.8h, v20.8h, v31.8h
        add	v31.8h, v4.8h, v3.8h
        mul	v26.8h, v13.8h, v0.h[2]
        str	q12, [x0, #0x30]
        sqrdmulh	v13.8h, v13.8h, v0.h[3]
        mul	v4.8h, v8.8h, v0.h[2]
        sqrdmulh	v8.8h, v8.8h, v0.h[3]
        mls	v26.8h, v13.8h, v7.h[0]
        mls	v18.8h, v21.8h, v7.h[0]
        mls	v4.8h, v8.8h, v7.h[0]
        sub	v20.8h, v26.8h, v11.8h
        sqrdmulh	v3.8h, v5.8h, v0.h[1]
        add	v6.8h, v26.8h, v11.8h
        sqrdmulh	v25.8h, v20.8h, v0.h[1]
        str	q18, [x0, #0xf0]
        sub	v18.8h, v4.8h, v23.8h
        add	v26.8h, v4.8h, v23.8h
        mul	v23.8h, v20.8h, v0.h[0]
        sqrdmulh	v11.8h, v18.8h, v0.h[1]
        str	q6, [x0, #0x70]
        mls	v23.8h, v25.8h, v7.h[0]
        str	q26, [x0, #0xb0]
        mul	v17.8h, v5.8h, v0.h[0]
        mul	v26.8h, v18.8h, v0.h[0]
        mls	v17.8h, v3.8h, v7.h[0]
        str	q23, [x0, #0x170]
        mls	v26.8h, v11.8h, v7.h[0]
        ldr	q3, [x0, #0xd0]
        mul	v23.8h, v27.8h, v0.h[4]
        mls	v23.8h, v10.8h, v7.h[0]
        str	q17, [x0, #0x130]
        str	q26, [x0, #0x1b0]
        subs	x4, x4, #0x1
        cbnz	x4, Lintt_layer123_start
        mls	v16.8h, v28.8h, v7.h[0]
        sub	v27.8h, v19.8h, v24.8h
        add	v12.8h, v22.8h, v29.8h
        ldr	q2, [x0]
        ldr	q10, [x0, #0x50]
        mul	v28.8h, v14.8h, v0.h[4]
        ldr	q22, [x0, #0x90]
        add	v21.8h, v19.8h, v24.8h
        ldr	q18, [x0, #0x10]
        sqrdmulh	v29.8h, v14.8h, v0.h[5]
        add	v24.8h, v2.8h, v15.8h
        ldr	q5, [x0, #0x110]
        sub	v26.8h, v2.8h, v15.8h
        sqrdmulh	v17.8h, v27.8h, v1.h[5]
        add	v30.8h, v22.8h, v3.8h
        sub	v4.8h, v22.8h, v3.8h
        sqrdmulh	v6.8h, v26.8h, v0.h[7]
        add	v25.8h, v24.8h, v31.8h
        ldr	q3, [x0, #0x150]
        sub	v22.8h, v24.8h, v31.8h
        mul	v11.8h, v26.8h, v0.h[6]
        add	v13.8h, v25.8h, v9.8h
        mls	v28.8h, v29.8h, v7.h[0]
        sub	v24.8h, v25.8h, v9.8h
        str	q13, [x0], #0x10
        add	v13.8h, v18.8h, v10.8h
        sub	v18.8h, v18.8h, v10.8h
        mls	v11.8h, v6.8h, v7.h[0]
        add	v19.8h, v5.8h, v3.8h
        sqrdmulh	v10.8h, v4.8h, v1.h[1]
        sub	v20.8h, v13.8h, v30.8h
        sub	v31.8h, v19.8h, v21.8h
        add	v14.8h, v19.8h, v21.8h
        sqrdmulh	v9.8h, v18.8h, v0.h[7]
        add	v6.8h, v13.8h, v30.8h
        sub	v21.8h, v5.8h, v3.8h
        mul	v3.8h, v27.8h, v1.h[4]
        sub	v5.8h, v6.8h, v14.8h
        mls	v3.8h, v17.8h, v7.h[0]
        sub	v26.8h, v11.8h, v16.8h
        add	v16.8h, v11.8h, v16.8h
        add	v30.8h, v6.8h, v14.8h
        sqrdmulh	v27.8h, v26.8h, v0.h[3]
        add	v11.8h, v16.8h, v12.8h
        sub	v8.8h, v16.8h, v12.8h
        mul	v16.8h, v26.8h, v0.h[2]
        str	q11, [x0, #0x30]
        str	q30, [x0], #0x10
        mul	v26.8h, v4.8h, v1.h[0]
        mls	v16.8h, v27.8h, v7.h[0]
        mul	v30.8h, v8.8h, v0.h[0]
        mul	v29.8h, v24.8h, v0.h[0]
        sub	v25.8h, v16.8h, v23.8h
        add	v11.8h, v16.8h, v23.8h
        mul	v27.8h, v22.8h, v0.h[2]
        sqrdmulh	v22.8h, v22.8h, v0.h[3]
        str	q11, [x0, #0xa0]
        mls	v26.8h, v10.8h, v7.h[0]
        mul	v17.8h, v31.8h, v0.h[4]
        sqrdmulh	v10.8h, v20.8h, v0.h[3]
        sqrdmulh	v13.8h, v31.8h, v0.h[5]
        mul	v14.8h, v20.8h, v0.h[2]
        sqrdmulh	v12.8h, v24.8h, v0.h[1]
        mls	v17.8h, v13.8h, v7.h[0]
        sqrdmulh	v20.8h, v21.8h, v1.h[3]
        sqrdmulh	v13.8h, v5.8h, v0.h[1]
        mul	v18.8h, v18.8h, v0.h[6]
        mul	v31.8h, v21.8h, v1.h[2]
        mul	v15.8h, v5.8h, v0.h[0]
        mls	v14.8h, v10.8h, v7.h[0]
        mls	v18.8h, v9.8h, v7.h[0]
        mul	v4.8h, v25.8h, v0.h[0]
        add	v5.8h, v14.8h, v17.8h
        mls	v27.8h, v22.8h, v7.h[0]
        sub	v9.8h, v14.8h, v17.8h
        str	q5, [x0, #0x70]
        mls	v31.8h, v20.8h, v7.h[0]
        sub	v17.8h, v18.8h, v26.8h
        add	v21.8h, v18.8h, v26.8h
        sqrdmulh	v18.8h, v9.8h, v0.h[1]
        add	v5.8h, v27.8h, v28.8h
        sqrdmulh	v10.8h, v17.8h, v0.h[3]
        sub	v16.8h, v27.8h, v28.8h
        str	q5, [x0, #0x60]
        add	v23.8h, v31.8h, v3.8h
        sub	v26.8h, v31.8h, v3.8h
        sqrdmulh	v5.8h, v16.8h, v0.h[1]
        add	v3.8h, v21.8h, v23.8h
        sqrdmulh	v6.8h, v25.8h, v0.h[1]
        str	q3, [x0, #0x30]
        sqrdmulh	v20.8h, v8.8h, v0.h[1]
        mul	v19.8h, v16.8h, v0.h[0]
        mul	v8.8h, v26.8h, v0.h[4]
        sub	v21.8h, v21.8h, v23.8h
        mul	v3.8h, v17.8h, v0.h[2]
        mul	v14.8h, v21.8h, v0.h[0]
        sqrdmulh	v17.8h, v26.8h, v0.h[5]
        mls	v3.8h, v10.8h, v7.h[0]
        mul	v16.8h, v9.8h, v0.h[0]
        mls	v8.8h, v17.8h, v7.h[0]
        mls	v29.8h, v12.8h, v7.h[0]
        mls	v16.8h, v18.8h, v7.h[0]
        mls	v30.8h, v20.8h, v7.h[0]
        sqrdmulh	v23.8h, v21.8h, v0.h[1]
        add	v21.8h, v3.8h, v8.8h
        mls	v4.8h, v6.8h, v7.h[0]
        str	q21, [x0, #0xb0]
        str	q30, [x0, #0x120]
        mls	v19.8h, v5.8h, v7.h[0]
        sub	v10.8h, v3.8h, v8.8h
        mls	v14.8h, v23.8h, v7.h[0]
        str	q4, [x0, #0x1a0]
        str	q29, [x0, #0xe0]
        sqrdmulh	v21.8h, v10.8h, v0.h[1]
        str	q16, [x0, #0x170]
        str	q19, [x0, #0x160]
        mls	v15.8h, v13.8h, v7.h[0]
        str	q14, [x0, #0x130]
        mul	v10.8h, v10.8h, v0.h[0]
        mls	v10.8h, v21.8h, v7.h[0]
        str	q15, [x0, #0xf0]
        str	q10, [x0, #0x1b0]
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
