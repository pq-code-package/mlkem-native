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

#include "../../../common.h"
#if defined(MLK_ARITH_BACKEND_AARCH64) &&  !defined(MLK_MULTILEVEL_BUILD_NO_SHARED)

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

scale_start:
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
        cbnz	x4, scale_start
        mov	x3, x0
        mov	x4, #0x8                // =8
        ldr	q17, [x3]
        ldr	q20, [x3, #0x10]
        ldr	q6, [x2, #0x50]
        trn1	v25.4s, v17.4s, v20.4s
        trn2	v17.4s, v17.4s, v20.4s
        ldr	q20, [x3, #0x20]
        ldr	q2, [x3, #0x30]
        ldr	q23, [x2, #0x10]
        trn2	v29.4s, v20.4s, v2.4s
        trn1	v20.4s, v20.4s, v2.4s
        ldr	q26, [x3, #0x50]
        trn2	v2.2d, v17.2d, v29.2d
        trn2	v10.2d, v25.2d, v20.2d
        trn1	v20.2d, v25.2d, v20.2d
        sub	v25.8h, v10.8h, v2.8h
        trn1	v17.2d, v17.2d, v29.2d
        add	v2.8h, v10.8h, v2.8h
        sqrdmulh	v6.8h, v25.8h, v6.8h
        sub	v29.8h, v20.8h, v17.8h
        ldr	q10, [x2, #0x30]
        ldr	q4, [x2, #0x20]
        sqrdmulh	v10.8h, v29.8h, v10.8h
        ldr	q13, [x2, #0x40]
        mul	v29.8h, v29.8h, v4.8h
        add	v17.8h, v20.8h, v17.8h
        mul	v20.8h, v25.8h, v13.8h
        ldr	q25, [x2], #0x60
        mls	v29.8h, v10.8h, v7.h[0]
        mls	v20.8h, v6.8h, v7.h[0]
        sub	v6.8h, v17.8h, v2.8h
        ldr	q13, [x3, #0x40]
        sub	v10.8h, v29.8h, v20.8h
        add	v17.8h, v17.8h, v2.8h
        sqrdmulh	v2.8h, v6.8h, v23.8h
        sqrdmulh	v23.8h, v10.8h, v23.8h
        add	v20.8h, v29.8h, v20.8h
        mul	v29.8h, v10.8h, v25.8h
        mul	v6.8h, v6.8h, v25.8h
        trn1	v25.4s, v17.4s, v20.4s
        trn2	v17.4s, v17.4s, v20.4s
        mls	v29.8h, v23.8h, v7.h[0]
        mls	v6.8h, v2.8h, v7.h[0]
        ldr	q4, [x1], #0x10
        trn2	v5.4s, v13.4s, v26.4s
        trn2	v2.4s, v6.4s, v29.4s
        trn1	v27.4s, v13.4s, v26.4s
        trn1	v6.4s, v6.4s, v29.4s
        trn1	v23.2d, v17.2d, v2.2d
        trn2	v17.2d, v17.2d, v2.2d
        trn2	v2.2d, v25.2d, v6.2d
        trn1	v6.2d, v25.2d, v6.2d
        add	v8.8h, v2.8h, v17.8h
        sub	v17.8h, v2.8h, v17.8h
        add	v19.8h, v6.8h, v23.8h
        sqdmulh	v18.8h, v8.8h, v7.h[1]
        sub	v25.8h, v6.8h, v23.8h
        mul	v0.8h, v17.8h, v4.h[4]
        sqrdmulh	v6.8h, v17.8h, v4.h[5]
        sqrdmulh	v2.8h, v25.8h, v4.h[3]
        mul	v10.8h, v25.8h, v4.h[2]
        srshr	v17.8h, v18.8h, #0xb
        mls	v0.8h, v6.8h, v7.h[0]
        sqdmulh	v25.8h, v19.8h, v7.h[1]
        mls	v10.8h, v2.8h, v7.h[0]
        ldr	q24, [x2, #0x50]
        srshr	v6.8h, v25.8h, #0xb
        add	v20.8h, v10.8h, v0.8h
        mls	v8.8h, v17.8h, v7.h[0]
        mls	v19.8h, v6.8h, v7.h[0]
        sqdmulh	v17.8h, v20.8h, v7.h[1]
        ldr	q2, [x3, #0x60]
        add	v6.8h, v19.8h, v8.8h
        srshr	v17.8h, v17.8h, #0xb
        ldr	q14, [x2, #0x10]
        sub	x4, x4, #0x2

layer4567_start:
        sub	v26.8h, v19.8h, v8.8h
        ldr	q30, [x3, #0x70]
        mul	v9.8h, v26.8h, v4.h[0]
        sqrdmulh	v16.8h, v26.8h, v4.h[1]
        trn2	v26.4s, v2.4s, v30.4s
        str	q6, [x3], #0x40
        mls	v20.8h, v17.8h, v7.h[0]
        trn2	v6.2d, v5.2d, v26.2d
        mls	v9.8h, v16.8h, v7.h[0]
        trn1	v31.4s, v2.4s, v30.4s
        stur	q20, [x3, #-0x30]
        trn1	v28.2d, v5.2d, v26.2d
        stur	q9, [x3, #-0x20]
        trn1	v9.2d, v27.2d, v31.2d
        ldr	q11, [x2, #0x30]
        sub	v21.8h, v9.8h, v28.8h
        ldr	q29, [x2, #0x20]
        sqrdmulh	v26.8h, v21.8h, v11.8h
        trn2	v8.2d, v27.2d, v31.2d
        mul	v13.8h, v21.8h, v29.8h
        sub	v18.8h, v8.8h, v6.8h
        ldr	q16, [x2, #0x40]
        mls	v13.8h, v26.8h, v7.h[0]
        sqrdmulh	v1.8h, v18.8h, v24.8h
        mul	v24.8h, v18.8h, v16.8h
        add	v21.8h, v8.8h, v6.8h
        add	v9.8h, v9.8h, v28.8h
        sub	v23.8h, v10.8h, v0.8h
        mls	v24.8h, v1.8h, v7.h[0]
        add	v18.8h, v9.8h, v21.8h
        ldr	q15, [x2], #0x60
        add	v8.8h, v13.8h, v24.8h
        sub	v28.8h, v13.8h, v24.8h
        sub	v24.8h, v9.8h, v21.8h
        trn1	v16.4s, v18.4s, v8.4s
        sqrdmulh	v31.8h, v28.8h, v14.8h
        mul	v11.8h, v28.8h, v15.8h
        sqrdmulh	v27.8h, v24.8h, v14.8h
        mul	v26.8h, v24.8h, v15.8h
        ldr	q19, [x3, #0x40]
        mls	v11.8h, v31.8h, v7.h[0]
        mls	v26.8h, v27.8h, v7.h[0]
        ldr	q24, [x3, #0x50]
        trn2	v5.4s, v18.4s, v8.4s
        trn2	v1.4s, v26.4s, v11.4s
        trn1	v27.4s, v19.4s, v24.4s
        trn1	v10.4s, v26.4s, v11.4s
        trn1	v22.2d, v5.2d, v1.2d
        trn2	v13.2d, v5.2d, v1.2d
        trn2	v5.4s, v19.4s, v24.4s
        trn2	v24.2d, v16.2d, v10.2d
        trn1	v31.2d, v16.2d, v10.2d
        add	v8.8h, v24.8h, v13.8h
        sub	v14.8h, v24.8h, v13.8h
        ldr	q24, [x2, #0x50]
        sub	v17.8h, v31.8h, v22.8h
        sqdmulh	v12.8h, v8.8h, v7.h[1]
        add	v19.8h, v31.8h, v22.8h
        sqrdmulh	v26.8h, v23.8h, v4.h[1]
        mul	v11.8h, v23.8h, v4.h[0]
        ldr	q4, [x1], #0x10
        srshr	v20.8h, v12.8h, #0xb
        sqdmulh	v22.8h, v19.8h, v7.h[1]
        sqrdmulh	v31.8h, v17.8h, v4.h[3]
        sqrdmulh	v18.8h, v14.8h, v4.h[5]
        mul	v0.8h, v14.8h, v4.h[4]
        mul	v10.8h, v17.8h, v4.h[2]
        mls	v8.8h, v20.8h, v7.h[0]
        srshr	v21.8h, v22.8h, #0xb
        mls	v0.8h, v18.8h, v7.h[0]
        mls	v10.8h, v31.8h, v7.h[0]
        mls	v19.8h, v21.8h, v7.h[0]
        ldr	q2, [x3, #0x60]
        add	v20.8h, v10.8h, v0.8h
        mls	v11.8h, v26.8h, v7.h[0]
        add	v6.8h, v19.8h, v8.8h
        sqdmulh	v17.8h, v20.8h, v7.h[1]
        ldr	q14, [x2, #0x10]
        stur	q11, [x3, #-0x10]
        srshr	v17.8h, v17.8h, #0xb
        sub	x4, x4, #0x1
        cbnz	x4, layer4567_start
        sub	v23.8h, v19.8h, v8.8h
        mls	v20.8h, v17.8h, v7.h[0]
        sub	v17.8h, v10.8h, v0.8h
        sqrdmulh	v15.8h, v23.8h, v4.h[1]
        mul	v18.8h, v23.8h, v4.h[0]
        sqrdmulh	v21.8h, v17.8h, v4.h[1]
        mul	v25.8h, v17.8h, v4.h[0]
        ldr	q23, [x3, #0x70]
        str	q6, [x3], #0x40
        ldr	q28, [x2, #0x40]
        trn2	v26.4s, v2.4s, v23.4s
        stur	q20, [x3, #-0x30]
        trn1	v29.4s, v2.4s, v23.4s
        trn1	v23.2d, v5.2d, v26.2d
        ldr	q20, [x2, #0x20]
        trn2	v16.2d, v27.2d, v29.2d
        trn2	v17.2d, v5.2d, v26.2d
        trn1	v19.2d, v27.2d, v29.2d
        sub	v31.8h, v16.8h, v17.8h
        add	v6.8h, v16.8h, v17.8h
        ldr	q17, [x2, #0x30]
        sqrdmulh	v9.8h, v31.8h, v24.8h
        sub	v11.8h, v19.8h, v23.8h
        mul	v26.8h, v31.8h, v28.8h
        add	v8.8h, v19.8h, v23.8h
        sqrdmulh	v10.8h, v11.8h, v17.8h
        mul	v30.8h, v11.8h, v20.8h
        add	v29.8h, v8.8h, v6.8h
        mls	v26.8h, v9.8h, v7.h[0]
        sub	v0.8h, v8.8h, v6.8h
        mls	v30.8h, v10.8h, v7.h[0]
        ldr	q9, [x2], #0x60
        sqrdmulh	v19.8h, v0.8h, v14.8h
        sub	v11.8h, v30.8h, v26.8h
        mls	v18.8h, v15.8h, v7.h[0]
        mul	v3.8h, v0.8h, v9.8h
        sqrdmulh	v5.8h, v11.8h, v14.8h
        mul	v20.8h, v11.8h, v9.8h
        stur	q18, [x3, #-0x20]
        mls	v3.8h, v19.8h, v7.h[0]
        add	v18.8h, v30.8h, v26.8h
        mls	v20.8h, v5.8h, v7.h[0]
        ldr	q6, [x1], #0x10
        trn1	v8.4s, v29.4s, v18.4s
        trn1	v2.4s, v3.4s, v20.4s
        trn2	v5.4s, v3.4s, v20.4s
        trn2	v0.4s, v29.4s, v18.4s
        trn2	v31.2d, v8.2d, v2.2d
        trn1	v23.2d, v8.2d, v2.2d
        trn1	v1.2d, v0.2d, v5.2d
        trn2	v13.2d, v0.2d, v5.2d
        add	v14.8h, v23.8h, v1.8h
        add	v27.8h, v31.8h, v13.8h
        sub	v4.8h, v31.8h, v13.8h
        sqdmulh	v28.8h, v14.8h, v7.h[1]
        sqdmulh	v30.8h, v27.8h, v7.h[1]
        sqrdmulh	v26.8h, v4.8h, v6.h[5]
        mul	v10.8h, v4.8h, v6.h[4]
        srshr	v0.8h, v28.8h, #0xb
        srshr	v30.8h, v30.8h, #0xb
        sub	v15.8h, v23.8h, v1.8h
        mls	v14.8h, v0.8h, v7.h[0]
        mls	v27.8h, v30.8h, v7.h[0]
        sqrdmulh	v20.8h, v15.8h, v6.h[3]
        mul	v8.8h, v15.8h, v6.h[2]
        mls	v25.8h, v21.8h, v7.h[0]
        mls	v10.8h, v26.8h, v7.h[0]
        sub	v2.8h, v14.8h, v27.8h
        mls	v8.8h, v20.8h, v7.h[0]
        stur	q25, [x3, #-0x10]
        add	v24.8h, v14.8h, v27.8h
        sqrdmulh	v19.8h, v2.8h, v6.h[1]
        add	v1.8h, v8.8h, v10.8h
        sub	v10.8h, v8.8h, v10.8h
        mul	v20.8h, v2.8h, v6.h[0]
        sqdmulh	v11.8h, v1.8h, v7.h[1]
        sqrdmulh	v17.8h, v10.8h, v6.h[1]
        mul	v3.8h, v10.8h, v6.h[0]
        mls	v20.8h, v19.8h, v7.h[0]
        srshr	v26.8h, v11.8h, #0xb
        str	q24, [x3], #0x40
        mls	v3.8h, v17.8h, v7.h[0]
        mls	v1.8h, v26.8h, v7.h[0]
        stur	q20, [x3, #-0x20]
        stur	q3, [x3, #-0x10]
        stur	q1, [x3, #-0x30]
        mov	x4, #0x4                // =4
        ldr	q0, [x1], #0x20
        ldur	q1, [x1, #-0x10]
        ldr	q29, [x0, #0x80]
        ldr	q2, [x0, #0xc0]
        ldr	q10, [x0, #0x100]
        ldr	q4, [x0, #0x140]
        ldr	q13, [x0, #0x180]
        ldr	q5, [x0, #0x1c0]
        add	v3.8h, v10.8h, v4.8h
        add	v27.8h, v29.8h, v2.8h
        add	v24.8h, v13.8h, v5.8h
        ldr	q25, [x0]
        add	v21.8h, v3.8h, v24.8h
        ldr	q23, [x0, #0x40]
        sub	x4, x4, #0x1

layer123_start:
        sub	v17.8h, v25.8h, v23.8h
        add	v20.8h, v25.8h, v23.8h
        sub	v6.8h, v29.8h, v2.8h
        sqrdmulh	v25.8h, v17.8h, v0.h[7]
        mul	v17.8h, v17.8h, v0.h[6]
        sub	v2.8h, v20.8h, v27.8h
        add	v20.8h, v20.8h, v27.8h
        sqrdmulh	v23.8h, v6.8h, v1.h[1]
        mul	v6.8h, v6.8h, v1.h[0]
        mls	v17.8h, v25.8h, v7.h[0]
        sub	v25.8h, v10.8h, v4.8h
        sqrdmulh	v29.8h, v2.8h, v0.h[3]
        mul	v2.8h, v2.8h, v0.h[2]
        sub	v10.8h, v20.8h, v21.8h
        add	v20.8h, v20.8h, v21.8h
        mls	v6.8h, v23.8h, v7.h[0]
        sqrdmulh	v23.8h, v25.8h, v1.h[3]
        mul	v25.8h, v25.8h, v1.h[2]
        sub	v4.8h, v13.8h, v5.8h
        sub	v13.8h, v17.8h, v6.8h
        add	v17.8h, v17.8h, v6.8h
        mls	v25.8h, v23.8h, v7.h[0]
        sqrdmulh	v6.8h, v4.8h, v1.h[5]
        mls	v2.8h, v29.8h, v7.h[0]
        mul	v23.8h, v4.8h, v1.h[4]
        sqrdmulh	v29.8h, v13.8h, v0.h[3]
        mul	v4.8h, v13.8h, v0.h[2]
        sqrdmulh	v13.8h, v10.8h, v0.h[1]
        mul	v10.8h, v10.8h, v0.h[0]
        str	q20, [x0], #0x10
        mls	v23.8h, v6.8h, v7.h[0]
        mls	v4.8h, v29.8h, v7.h[0]
        sub	v20.8h, v3.8h, v24.8h
        mls	v10.8h, v13.8h, v7.h[0]
        sub	v6.8h, v25.8h, v23.8h
        sqrdmulh	v29.8h, v20.8h, v0.h[5]
        mul	v20.8h, v20.8h, v0.h[4]
        add	v25.8h, v25.8h, v23.8h
        sqrdmulh	v23.8h, v6.8h, v0.h[5]
        mul	v6.8h, v6.8h, v0.h[4]
        mls	v20.8h, v29.8h, v7.h[0]
        sub	v29.8h, v17.8h, v25.8h
        add	v17.8h, v17.8h, v25.8h
        mls	v6.8h, v23.8h, v7.h[0]
        sqrdmulh	v25.8h, v29.8h, v0.h[1]
        mul	v23.8h, v29.8h, v0.h[0]
        sub	v29.8h, v2.8h, v20.8h
        add	v20.8h, v2.8h, v20.8h
        sub	v2.8h, v4.8h, v6.8h
        mls	v23.8h, v25.8h, v7.h[0]
        sqrdmulh	v25.8h, v29.8h, v0.h[1]
        mul	v29.8h, v29.8h, v0.h[0]
        add	v6.8h, v4.8h, v6.8h
        sqrdmulh	v4.8h, v2.8h, v0.h[1]
        mul	v2.8h, v2.8h, v0.h[0]
        mls	v29.8h, v25.8h, v7.h[0]
        str	q10, [x0, #0xf0]
        ldr	q25, [x0]
        mls	v2.8h, v4.8h, v7.h[0]
        str	q23, [x0, #0x130]
        ldr	q23, [x0, #0x40]
        str	q29, [x0, #0x170]
        ldr	q29, [x0, #0x80]
        str	q2, [x0, #0x1b0]
        ldr	q2, [x0, #0xc0]
        str	q17, [x0, #0x30]
        ldr	q10, [x0, #0x100]
        ldr	q4, [x0, #0x140]
        ldr	q13, [x0, #0x180]
        ldr	q5, [x0, #0x1c0]
        str	q20, [x0, #0x70]
        add	v3.8h, v10.8h, v4.8h
        add	v24.8h, v13.8h, v5.8h
        str	q6, [x0, #0xb0]
        add	v27.8h, v29.8h, v2.8h
        add	v21.8h, v3.8h, v24.8h
        sub	x4, x4, #0x1
        cbnz	x4, layer123_start
        add	v22.8h, v25.8h, v23.8h
        sub	v17.8h, v3.8h, v24.8h
        sub	v25.8h, v25.8h, v23.8h
        sub	v19.8h, v22.8h, v27.8h
        mul	v28.8h, v17.8h, v0.h[4]
        sqrdmulh	v20.8h, v17.8h, v0.h[5]
        sqrdmulh	v17.8h, v19.8h, v0.h[3]
        mul	v24.8h, v19.8h, v0.h[2]
        sub	v31.8h, v29.8h, v2.8h
        sqrdmulh	v19.8h, v25.8h, v0.h[7]
        mls	v28.8h, v20.8h, v7.h[0]
        mls	v24.8h, v17.8h, v7.h[0]
        sqrdmulh	v9.8h, v31.8h, v1.h[1]
        mul	v26.8h, v31.8h, v1.h[0]
        mul	v23.8h, v25.8h, v0.h[6]
        sub	v17.8h, v24.8h, v28.8h
        sub	v5.8h, v13.8h, v5.8h
        mls	v26.8h, v9.8h, v7.h[0]
        sqrdmulh	v20.8h, v17.8h, v0.h[1]
        mul	v17.8h, v17.8h, v0.h[0]
        mls	v23.8h, v19.8h, v7.h[0]
        sqrdmulh	v6.8h, v5.8h, v1.h[5]
        mul	v5.8h, v5.8h, v1.h[4]
        mls	v17.8h, v20.8h, v7.h[0]
        sub	v16.8h, v23.8h, v26.8h
        sub	v3.8h, v10.8h, v4.8h
        mls	v5.8h, v6.8h, v7.h[0]
        mul	v29.8h, v16.8h, v0.h[2]
        sqrdmulh	v6.8h, v16.8h, v0.h[3]
        sqrdmulh	v4.8h, v3.8h, v1.h[3]
        add	v27.8h, v22.8h, v27.8h
        mul	v3.8h, v3.8h, v1.h[2]
        mls	v29.8h, v6.8h, v7.h[0]
        sub	v25.8h, v27.8h, v21.8h
        str	q17, [x0, #0x180]
        mls	v3.8h, v4.8h, v7.h[0]
        sqrdmulh	v2.8h, v25.8h, v0.h[1]
        mul	v10.8h, v25.8h, v0.h[0]
        add	v4.8h, v23.8h, v26.8h
        add	v20.8h, v3.8h, v5.8h
        sub	v23.8h, v3.8h, v5.8h
        mls	v10.8h, v2.8h, v7.h[0]
        add	v13.8h, v4.8h, v20.8h
        mul	v6.8h, v23.8h, v0.h[4]
        sqrdmulh	v23.8h, v23.8h, v0.h[5]
        str	q10, [x0, #0x100]
        sub	v9.8h, v4.8h, v20.8h
        str	q13, [x0, #0x40]
        mls	v6.8h, v23.8h, v7.h[0]
        sqrdmulh	v23.8h, v9.8h, v0.h[1]
        mul	v25.8h, v9.8h, v0.h[0]
        add	v2.8h, v24.8h, v28.8h
        sub	v17.8h, v29.8h, v6.8h
        add	v6.8h, v29.8h, v6.8h
        mls	v25.8h, v23.8h, v7.h[0]
        sqrdmulh	v20.8h, v17.8h, v0.h[1]
        mul	v17.8h, v17.8h, v0.h[0]
        str	q6, [x0, #0xc0]
        add	v23.8h, v27.8h, v21.8h
        str	q25, [x0, #0x140]
        mls	v17.8h, v20.8h, v7.h[0]
        str	q23, [x0], #0x10
        str	q2, [x0, #0x70]
        str	q17, [x0, #0x1b0]
        ldp	d8, d9, [sp]
        ldp	d10, d11, [sp, #0x10]
        ldp	d12, d13, [sp, #0x20]
        ldp	d14, d15, [sp, #0x30]
        add	sp, sp, #0x40
        ret

#endif /* MLK_ARITH_BACKEND_AARCH64 && !MLK_MULTILEVEL_BUILD_NO_SHARED */
