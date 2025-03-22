/// Copyright (c) 2024-2025 The mlkem-native project authors
/// Copyright (c) 2022 Arm Limited
/// Copyright (c) 2022 Hanno Becker
/// Copyright (c) 2023 Amin Abdulrahman, Matthias Kannwischer
/// SPDX-License-Identifier: MIT
///
/// Permission is hereby granted, free of charge, to any person obtaining a copy
/// of this software and associated documentation files (the "Software"), to deal
/// in the Software without restriction, including without limitation the rights
/// to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
/// copies of the Software, and to permit persons to whom the Software is
/// furnished to do so, subject to the following conditions:
///
/// The above copyright notice and this permission notice shall be included in all
/// copies or substantial portions of the Software.
///
/// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
/// IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
/// FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
/// AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
/// LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
/// OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
/// SOFTWARE.
///


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
        mov	v7.h[2], w5
        mov	w5, #0x13b0             // =5040
        mov	v7.h[3], w5
        mov	x3, x0
        mov	x4, #0x8                // =8
        ldr	q10, [x3, #0x20]
        ldr	q13, [x3]
        ldr	q3, [x3, #0x10]
        ldr	q12, [x3, #0x30]
        trn1	v6.4s, v13.4s, v3.4s
        trn2	v21.4s, v13.4s, v3.4s
        trn1	v13.4s, v10.4s, v12.4s
        trn2	v12.4s, v10.4s, v12.4s
        ldr	q22, [x2, #0x50]
        trn1	v9.2d, v6.2d, v13.2d
        trn2	v24.2d, v21.2d, v12.2d
        trn1	v3.2d, v21.2d, v12.2d
        trn2	v31.2d, v6.2d, v13.2d
        add	v21.8h, v9.8h, v3.8h
        add	v1.8h, v31.8h, v24.8h
        sub	v27.8h, v31.8h, v24.8h
        ldr	q17, [x2, #0x20]
        ldr	q6, [x2, #0x40]
        sub	v31.8h, v9.8h, v3.8h
        ldr	q12, [x2, #0x30]
        mul	v14.8h, v31.8h, v17.8h
        sqrdmulh	v3.8h, v27.8h, v22.8h
        mul	v11.8h, v27.8h, v6.8h
        sqrdmulh	v13.8h, v31.8h, v12.8h
        ldr	q20, [x2, #0x10]
        mls	v11.8h, v3.8h, v7.h[0]
        mls	v14.8h, v13.8h, v7.h[0]
        sub	v15.8h, v21.8h, v1.8h
        ldr	q10, [x2], #0x60
        sub	v6.8h, v14.8h, v11.8h
        sqrdmulh	v5.8h, v15.8h, v20.8h
        mul	v16.8h, v15.8h, v10.8h
        mul	v15.8h, v6.8h, v10.8h
        sqrdmulh	v13.8h, v6.8h, v20.8h
        add	v12.8h, v21.8h, v1.8h
        add	v31.8h, v14.8h, v11.8h
        mls	v16.8h, v5.8h, v7.h[0]
        mls	v15.8h, v13.8h, v7.h[0]
        ldr	q6, [x1], #0x10
        trn1	v5.4s, v12.4s, v31.4s
        trn1	v13.4s, v16.4s, v15.4s
        trn2	v31.4s, v12.4s, v31.4s
        trn2	v12.4s, v16.4s, v15.4s
        trn1	v3.2d, v5.2d, v13.2d
        trn2	v13.2d, v5.2d, v13.2d
        trn1	v21.2d, v31.2d, v12.2d
        trn2	v10.2d, v31.2d, v12.2d
        add	v11.8h, v3.8h, v21.8h
        add	v8.8h, v13.8h, v10.8h
        sub	v13.8h, v13.8h, v10.8h
        sub	v3.8h, v3.8h, v21.8h
        sqdmulh	v21.8h, v11.8h, v7.h[1]
        sqrdmulh	v10.8h, v13.8h, v6.h[5]
        mul	v14.8h, v3.8h, v6.h[2]
        mul	v15.8h, v13.8h, v6.h[4]
        sqrdmulh	v13.8h, v3.8h, v6.h[3]
        sqdmulh	v12.8h, v8.8h, v7.h[1]
        srshr	v4.8h, v21.8h, #0xb
        mls	v15.8h, v10.8h, v7.h[0]
        mls	v14.8h, v13.8h, v7.h[0]
        mls	v11.8h, v4.8h, v7.h[0]
        srshr	v12.8h, v12.8h, #0xb
        sub	v16.8h, v14.8h, v15.8h
        sub	x4, x4, #0x1

layer4567_start:
        mul	v17.8h, v16.8h, v6.h[0]
        ldr	q2, [x2, #0x20]
        ldr	q1, [x3, #0x50]
        sqrdmulh	v21.8h, v16.8h, v6.h[1]
        mls	v8.8h, v12.8h, v7.h[0]
        ldr	q19, [x3, #0x40]
        mls	v17.8h, v21.8h, v7.h[0]
        sub	v27.8h, v11.8h, v8.8h
        trn1	v23.4s, v19.4s, v1.4s
        trn2	v20.4s, v19.4s, v1.4s
        ldr	q18, [x3, #0x60]
        ldr	q28, [x3, #0x70]
        add	v22.8h, v14.8h, v15.8h
        str	q17, [x3, #0x30]
        add	v3.8h, v11.8h, v8.8h
        trn1	v15.4s, v18.4s, v28.4s
        trn2	v0.4s, v18.4s, v28.4s
        sqrdmulh	v9.8h, v27.8h, v6.h[1]
        trn1	v11.2d, v23.2d, v15.2d
        trn2	v17.2d, v23.2d, v15.2d
        trn2	v1.2d, v20.2d, v0.2d
        trn1	v14.2d, v20.2d, v0.2d
        sub	v5.8h, v17.8h, v1.8h
        sub	v13.8h, v11.8h, v14.8h
        ldr	q25, [x2, #0x50]
        ldr	q24, [x2, #0x30]
        ldr	q21, [x2, #0x40]
        mul	v0.8h, v27.8h, v6.h[0]
        sqrdmulh	v6.8h, v5.8h, v25.8h
        mul	v28.8h, v5.8h, v21.8h
        add	v8.8h, v17.8h, v1.8h
        sqrdmulh	v1.8h, v13.8h, v24.8h
        mul	v16.8h, v13.8h, v2.8h
        mls	v28.8h, v6.8h, v7.h[0]
        ldr	q6, [x2, #0x10]
        add	v24.8h, v11.8h, v14.8h
        mls	v16.8h, v1.8h, v7.h[0]
        sqdmulh	v12.8h, v22.8h, v7.h[1]
        ldr	q15, [x2], #0x60
        sub	v31.8h, v16.8h, v28.8h
        sub	v13.8h, v24.8h, v8.8h
        add	v26.8h, v24.8h, v8.8h
        sqrdmulh	v20.8h, v31.8h, v6.8h
        mul	v1.8h, v13.8h, v15.8h
        mul	v14.8h, v31.8h, v15.8h
        sqrdmulh	v15.8h, v13.8h, v6.8h
        add	v13.8h, v16.8h, v28.8h
        ldr	q6, [x1], #0x10
        mls	v1.8h, v15.8h, v7.h[0]
        srshr	v18.8h, v12.8h, #0xb
        mls	v14.8h, v20.8h, v7.h[0]
        trn1	v21.4s, v26.4s, v13.4s
        trn2	v11.4s, v26.4s, v13.4s
        mls	v22.8h, v18.8h, v7.h[0]
        trn1	v17.4s, v1.4s, v14.4s
        trn2	v13.4s, v1.4s, v14.4s
        mls	v0.8h, v9.8h, v7.h[0]
        trn2	v31.2d, v21.2d, v17.2d
        trn1	v25.2d, v21.2d, v17.2d
        trn1	v2.2d, v11.2d, v13.2d
        trn2	v16.2d, v11.2d, v13.2d
        add	v11.8h, v25.8h, v2.8h
        add	v8.8h, v31.8h, v16.8h
        sub	v1.8h, v31.8h, v16.8h
        sub	v17.8h, v25.8h, v2.8h
        sqdmulh	v16.8h, v11.8h, v7.h[1]
        sqrdmulh	v5.8h, v1.8h, v6.h[5]
        mul	v15.8h, v1.8h, v6.h[4]
        mul	v14.8h, v17.8h, v6.h[2]
        sqrdmulh	v9.8h, v17.8h, v6.h[3]
        srshr	v31.8h, v16.8h, #0xb
        mls	v15.8h, v5.8h, v7.h[0]
        str	q0, [x3, #0x20]
        mls	v14.8h, v9.8h, v7.h[0]
        sqdmulh	v19.8h, v8.8h, v7.h[1]
        mls	v11.8h, v31.8h, v7.h[0]
        str	q22, [x3, #0x10]
        sub	v16.8h, v14.8h, v15.8h
        str	q3, [x3], #0x40
        srshr	v12.8h, v19.8h, #0xb
        sub	x4, x4, #0x1
        cbnz	x4, layer4567_start
        mls	v8.8h, v12.8h, v7.h[0]
        add	v12.8h, v14.8h, v15.8h
        sqrdmulh	v0.8h, v16.8h, v6.h[1]
        mul	v16.8h, v16.8h, v6.h[0]
        sub	v26.8h, v11.8h, v8.8h
        add	v11.8h, v11.8h, v8.8h
        sqdmulh	v23.8h, v12.8h, v7.h[1]
        sqrdmulh	v14.8h, v26.8h, v6.h[1]
        mul	v15.8h, v26.8h, v6.h[0]
        mls	v16.8h, v0.8h, v7.h[0]
        srshr	v22.8h, v23.8h, #0xb
        str	q11, [x3], #0x40
        mls	v15.8h, v14.8h, v7.h[0]
        mls	v12.8h, v22.8h, v7.h[0]
        stur	q16, [x3, #-0x10]
        stur	q15, [x3, #-0x20]
        stur	q12, [x3, #-0x30]
        mov	x4, #0x4                // =4
        ldr	q0, [x1], #0x20
        ldur	q1, [x1, #-0x10]
        ldr	q15, [x0]
        ldr	q9, [x0, #0xc0]
        ldr	q10, [x0, #0x80]
        ldr	q25, [x0, #0x40]
        sub	v31.8h, v10.8h, v9.8h
        add	v12.8h, v10.8h, v9.8h
        add	v21.8h, v15.8h, v25.8h
        ldr	q18, [x0, #0x1c0]
        sub	v13.8h, v21.8h, v12.8h
        ldr	q28, [x0, #0x180]
        sqrdmulh	v5.8h, v13.8h, v0.h[3]
        ldr	q10, [x0, #0x140]
        sub	v6.8h, v28.8h, v18.8h
        ldr	q3, [x0, #0x100]
        mul	v19.8h, v6.8h, v1.h[4]
        sqrdmulh	v24.8h, v6.8h, v1.h[5]
        sub	v9.8h, v15.8h, v25.8h
        add	v27.8h, v3.8h, v10.8h
        sub	v20.8h, v3.8h, v10.8h
        mul	v4.8h, v9.8h, v0.h[6]
        sqrdmulh	v25.8h, v9.8h, v0.h[7]
        add	v10.8h, v28.8h, v18.8h
        sqrdmulh	v15.8h, v20.8h, v1.h[3]
        add	v6.8h, v21.8h, v12.8h
        add	v9.8h, v27.8h, v10.8h
        mul	v12.8h, v20.8h, v1.h[2]
        sub	v10.8h, v27.8h, v10.8h
        mls	v19.8h, v24.8h, v7.h[0]
        mls	v4.8h, v25.8h, v7.h[0]
        mul	v16.8h, v13.8h, v0.h[2]
        mls	v12.8h, v15.8h, v7.h[0]
        sqrdmulh	v21.8h, v31.8h, v1.h[1]
        mul	v13.8h, v31.8h, v1.h[0]
        sub	v27.8h, v6.8h, v9.8h
        sub	v3.8h, v12.8h, v19.8h
        add	v31.8h, v12.8h, v19.8h
        mls	v13.8h, v21.8h, v7.h[0]
        add	v2.8h, v6.8h, v9.8h
        mul	v11.8h, v10.8h, v0.h[4]
        sqrdmulh	v22.8h, v10.8h, v0.h[5]
        add	v20.8h, v4.8h, v13.8h
        sub	v12.8h, v4.8h, v13.8h
        ldr	q15, [x0, #0x190]
        add	v25.8h, v20.8h, v31.8h
        ldr	q13, [x0, #0x150]
        mul	v19.8h, v25.8h, v7.h[2]
        sqrdmulh	v28.8h, v25.8h, v7.h[3]
        ldr	q25, [x0, #0x50]
        sqrdmulh	v4.8h, v12.8h, v0.h[3]
        mls	v19.8h, v28.8h, v7.h[0]
        ldr	q21, [x0, #0x1d0]
        sub	x4, x4, #0x2

layer123_start:
        sub	v23.8h, v20.8h, v31.8h
        ldr	q24, [x0, #0x10]
        ldr	q9, [x0, #0xd0]
        sub	v31.8h, v15.8h, v21.8h
        sub	v20.8h, v24.8h, v25.8h
        ldr	q14, [x0, #0x110]
        mul	v8.8h, v20.8h, v0.h[6]
        mul	v17.8h, v31.8h, v1.h[4]
        sqrdmulh	v28.8h, v31.8h, v1.h[5]
        add	v26.8h, v14.8h, v13.8h
        sub	v10.8h, v14.8h, v13.8h
        mls	v11.8h, v22.8h, v7.h[0]
        mul	v18.8h, v12.8h, v0.h[2]
        mls	v16.8h, v5.8h, v7.h[0]
        sqrdmulh	v12.8h, v27.8h, v1.h[7]
        sqrdmulh	v14.8h, v20.8h, v0.h[7]
        mls	v18.8h, v4.8h, v7.h[0]
        sqrdmulh	v13.8h, v2.8h, v7.h[3]
        add	v5.8h, v16.8h, v11.8h
        mul	v4.8h, v27.8h, v1.h[6]
        mul	v2.8h, v2.8h, v7.h[2]
        sqrdmulh	v20.8h, v3.8h, v0.h[5]
        ldr	q22, [x0, #0x90]
        sqrdmulh	v27.8h, v10.8h, v1.h[3]
        mls	v4.8h, v12.8h, v7.h[0]
        sub	v12.8h, v22.8h, v9.8h
        add	v31.8h, v22.8h, v9.8h
        add	v21.8h, v15.8h, v21.8h
        add	v9.8h, v24.8h, v25.8h
        sqrdmulh	v15.8h, v12.8h, v1.h[1]
        add	v25.8h, v26.8h, v21.8h
        add	v22.8h, v9.8h, v31.8h
        mul	v24.8h, v10.8h, v1.h[2]
        sub	v10.8h, v26.8h, v21.8h
        sub	v9.8h, v9.8h, v31.8h
        mls	v17.8h, v28.8h, v7.h[0]
        mul	v26.8h, v23.8h, v1.h[6]
        mls	v8.8h, v14.8h, v7.h[0]
        sqrdmulh	v28.8h, v23.8h, v1.h[7]
        sub	v14.8h, v16.8h, v11.8h
        mul	v16.8h, v9.8h, v0.h[2]
        mul	v23.8h, v3.8h, v0.h[4]
        str	q4, [x0, #0x100]
        mls	v26.8h, v28.8h, v7.h[0]
        mls	v24.8h, v27.8h, v7.h[0]
        mls	v23.8h, v20.8h, v7.h[0]
        sqrdmulh	v6.8h, v14.8h, v0.h[1]
        sub	v27.8h, v22.8h, v25.8h
        str	q26, [x0, #0x140]
        sub	v28.8h, v18.8h, v23.8h
        add	v26.8h, v18.8h, v23.8h
        mul	v23.8h, v14.8h, v0.h[0]
        sqrdmulh	v4.8h, v28.8h, v0.h[1]
        mul	v11.8h, v28.8h, v0.h[0]
        sub	v3.8h, v24.8h, v17.8h
        mul	v18.8h, v12.8h, v1.h[0]
        mls	v2.8h, v13.8h, v7.h[0]
        mls	v11.8h, v4.8h, v7.h[0]
        ldr	q21, [x0, #0x1e0]
        mls	v23.8h, v6.8h, v7.h[0]
        str	q11, [x0, #0x1c0]
        mls	v18.8h, v15.8h, v7.h[0]
        str	q5, [x0, #0x80]
        add	v31.8h, v24.8h, v17.8h
        sqrdmulh	v5.8h, v9.8h, v0.h[3]
        str	q2, [x0], #0x10
        add	v2.8h, v22.8h, v25.8h
        add	v20.8h, v8.8h, v18.8h
        sub	v12.8h, v8.8h, v18.8h
        str	q23, [x0, #0x170]
        mul	v11.8h, v10.8h, v0.h[4]
        sqrdmulh	v22.8h, v10.8h, v0.h[5]
        str	q26, [x0, #0xb0]
        ldr	q15, [x0, #0x190]
        str	q19, [x0, #0x30]
        add	v9.8h, v20.8h, v31.8h
        ldr	q13, [x0, #0x150]
        mul	v19.8h, v9.8h, v7.h[2]
        sqrdmulh	v18.8h, v9.8h, v7.h[3]
        ldr	q25, [x0, #0x50]
        sqrdmulh	v4.8h, v12.8h, v0.h[3]
        mls	v19.8h, v18.8h, v7.h[0]
        sub	x4, x4, #0x1
        cbnz	x4, layer123_start
        mls	v11.8h, v22.8h, v7.h[0]
        add	v18.8h, v15.8h, v21.8h
        sub	v21.8h, v15.8h, v21.8h
        sqrdmulh	v9.8h, v2.8h, v7.h[3]
        mul	v23.8h, v2.8h, v7.h[2]
        mls	v16.8h, v5.8h, v7.h[0]
        sub	v2.8h, v20.8h, v31.8h
        mul	v15.8h, v12.8h, v0.h[2]
        str	q19, [x0, #0x40]
        ldr	q6, [x0, #0x110]
        sqrdmulh	v12.8h, v27.8h, v1.h[7]
        mul	v19.8h, v27.8h, v1.h[6]
        sub	v20.8h, v6.8h, v13.8h
        add	v27.8h, v6.8h, v13.8h
        mls	v15.8h, v4.8h, v7.h[0]
        add	v5.8h, v16.8h, v11.8h
        sub	v16.8h, v16.8h, v11.8h
        ldr	q13, [x0, #0x10]
        mul	v4.8h, v3.8h, v0.h[4]
        sqrdmulh	v31.8h, v3.8h, v0.h[5]
        add	v28.8h, v13.8h, v25.8h
        sub	v3.8h, v13.8h, v25.8h
        mls	v23.8h, v9.8h, v7.h[0]
        add	v13.8h, v27.8h, v18.8h
        sub	v6.8h, v27.8h, v18.8h
        sqrdmulh	v22.8h, v21.8h, v1.h[5]
        mul	v27.8h, v21.8h, v1.h[4]
        sqrdmulh	v24.8h, v2.8h, v1.h[7]
        mul	v26.8h, v2.8h, v1.h[6]
        mls	v19.8h, v12.8h, v7.h[0]
        mul	v21.8h, v20.8h, v1.h[2]
        sqrdmulh	v10.8h, v20.8h, v1.h[3]
        str	q5, [x0, #0x80]
        mls	v4.8h, v31.8h, v7.h[0]
        sqrdmulh	v2.8h, v16.8h, v0.h[1]
        mul	v25.8h, v16.8h, v0.h[0]
        mls	v21.8h, v10.8h, v7.h[0]
        sub	v9.8h, v15.8h, v4.8h
        add	v17.8h, v15.8h, v4.8h
        mul	v31.8h, v3.8h, v0.h[6]
        mls	v27.8h, v22.8h, v7.h[0]
        sqrdmulh	v8.8h, v6.8h, v0.h[5]
        sqrdmulh	v14.8h, v3.8h, v0.h[7]
        sqrdmulh	v3.8h, v9.8h, v0.h[1]
        sub	v15.8h, v21.8h, v27.8h
        add	v27.8h, v21.8h, v27.8h
        ldr	q20, [x0, #0xd0]
        ldr	q5, [x0, #0x90]
        mul	v4.8h, v6.8h, v0.h[4]
        mul	v18.8h, v15.8h, v0.h[4]
        add	v11.8h, v5.8h, v20.8h
        mls	v31.8h, v14.8h, v7.h[0]
        str	q23, [x0], #0x10
        add	v16.8h, v28.8h, v11.8h
        sub	v10.8h, v28.8h, v11.8h
        mls	v26.8h, v24.8h, v7.h[0]
        sub	v28.8h, v16.8h, v13.8h
        add	v16.8h, v16.8h, v13.8h
        mul	v22.8h, v10.8h, v0.h[2]
        str	q19, [x0, #0xf0]
        mls	v4.8h, v8.8h, v7.h[0]
        mul	v19.8h, v16.8h, v7.h[2]
        sqrdmulh	v10.8h, v10.8h, v0.h[3]
        mul	v12.8h, v28.8h, v1.h[6]
        sqrdmulh	v28.8h, v28.8h, v1.h[7]
        sqrdmulh	v15.8h, v15.8h, v0.h[5]
        mls	v22.8h, v10.8h, v7.h[0]
        mls	v25.8h, v2.8h, v7.h[0]
        mul	v2.8h, v9.8h, v0.h[0]
        mls	v12.8h, v28.8h, v7.h[0]
        add	v23.8h, v22.8h, v4.8h
        sqrdmulh	v13.8h, v16.8h, v7.h[3]
        sub	v6.8h, v5.8h, v20.8h
        str	q23, [x0, #0x80]
        mls	v18.8h, v15.8h, v7.h[0]
        mls	v19.8h, v13.8h, v7.h[0]
        str	q17, [x0, #0xb0]
        mul	v16.8h, v6.8h, v1.h[0]
        sqrdmulh	v10.8h, v6.8h, v1.h[1]
        str	q12, [x0, #0x100]
        mls	v2.8h, v3.8h, v7.h[0]
        str	q25, [x0, #0x170]
        mls	v16.8h, v10.8h, v7.h[0]
        str	q26, [x0, #0x130]
        sub	v24.8h, v22.8h, v4.8h
        str	q2, [x0, #0x1b0]
        add	v21.8h, v31.8h, v16.8h
        sub	v14.8h, v31.8h, v16.8h
        mul	v20.8h, v24.8h, v0.h[0]
        add	v17.8h, v21.8h, v27.8h
        sub	v9.8h, v21.8h, v27.8h
        sqrdmulh	v23.8h, v14.8h, v0.h[3]
        mul	v15.8h, v14.8h, v0.h[2]
        sqrdmulh	v6.8h, v17.8h, v7.h[3]
        mul	v13.8h, v17.8h, v7.h[2]
        mul	v21.8h, v9.8h, v1.h[6]
        mls	v15.8h, v23.8h, v7.h[0]
        sqrdmulh	v22.8h, v9.8h, v1.h[7]
        mls	v13.8h, v6.8h, v7.h[0]
        sqrdmulh	v26.8h, v24.8h, v0.h[1]
        str	q19, [x0], #0x10
        mls	v21.8h, v22.8h, v7.h[0]
        sub	v3.8h, v15.8h, v18.8h
        str	q13, [x0, #0x30]
        mls	v20.8h, v26.8h, v7.h[0]
        sqrdmulh	v8.8h, v3.8h, v0.h[1]
        mul	v2.8h, v3.8h, v0.h[0]
        str	q21, [x0, #0x130]
        add	v23.8h, v15.8h, v18.8h
        str	q20, [x0, #0x170]
        mls	v2.8h, v8.8h, v7.h[0]
        str	q23, [x0, #0xb0]
        str	q2, [x0, #0x1b0]
        ldp	d8, d9, [sp]
        ldp	d10, d11, [sp, #0x10]
        ldp	d12, d13, [sp, #0x20]
        ldp	d14, d15, [sp, #0x30]
        add	sp, sp, #0x40
        ret
