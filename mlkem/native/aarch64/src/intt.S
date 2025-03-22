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
        mov	v7.h[2], w5
        mov	w5, #0x13b0             // =5040
        mov	v7.h[3], w5
        mov	x3, x0
        mov	x4, #0x8                // =8
        ldr	q26, [x3, #0x20]
        ldr	q3, [x3, #0x10]
        ldr	q13, [x3, #0x30]
        ldr	q27, [x3]
        trn2	v10.4s, v26.4s, v13.4s
        trn1	v13.4s, v26.4s, v13.4s
        trn2	v21.4s, v27.4s, v3.4s
        ldr	q1, [x2, #0x40]
        trn2	v16.2d, v21.2d, v10.2d
        trn1	v27.4s, v27.4s, v3.4s
        ldr	q5, [x2, #0x30]
        trn1	v12.2d, v27.2d, v13.2d
        trn2	v2.2d, v27.2d, v13.2d
        trn1	v6.2d, v21.2d, v10.2d
        sub	v27.8h, v2.8h, v16.8h
        sub	v3.8h, v12.8h, v6.8h
        ldr	q21, [x2, #0x50]
        sqrdmulh	v10.8h, v3.8h, v5.8h
        ldr	q13, [x2, #0x20]
        mul	v29.8h, v27.8h, v1.8h
        sqrdmulh	v31.8h, v27.8h, v21.8h
        mul	v22.8h, v3.8h, v13.8h
        add	v13.8h, v12.8h, v6.8h
        add	v28.8h, v2.8h, v16.8h
        mls	v29.8h, v31.8h, v7.h[0]
        mls	v22.8h, v10.8h, v7.h[0]
        ldr	q1, [x2], #0x60
        sub	v25.8h, v13.8h, v28.8h
        sub	v20.8h, v22.8h, v29.8h
        ldur	q10, [x2, #-0x50]
        mul	v27.8h, v20.8h, v1.8h
        mul	v1.8h, v25.8h, v1.8h
        sqrdmulh	v3.8h, v25.8h, v10.8h
        sqrdmulh	v12.8h, v20.8h, v10.8h
        add	v15.8h, v13.8h, v28.8h
        add	v9.8h, v22.8h, v29.8h
        mls	v1.8h, v3.8h, v7.h[0]
        mls	v27.8h, v12.8h, v7.h[0]
        trn1	v3.4s, v15.4s, v9.4s
        trn2	v5.4s, v15.4s, v9.4s
        trn1	v13.4s, v1.4s, v27.4s
        trn2	v31.4s, v1.4s, v27.4s
        trn2	v10.2d, v3.2d, v13.2d
        trn1	v30.2d, v5.2d, v31.2d
        trn2	v21.2d, v5.2d, v31.2d
        trn1	v3.2d, v3.2d, v13.2d
        add	v22.8h, v10.8h, v21.8h
        add	v29.8h, v3.8h, v30.8h
        sqdmulh	v20.8h, v22.8h, v7.h[1]
        sqdmulh	v27.8h, v29.8h, v7.h[1]
        sub	v1.8h, v3.8h, v30.8h
        srshr	v13.8h, v20.8h, #0xb
        srshr	v11.8h, v27.8h, #0xb
        sub	v27.8h, v10.8h, v21.8h
        mls	v22.8h, v13.8h, v7.h[0]
        mls	v29.8h, v11.8h, v7.h[0]
        sub	x4, x4, #0x1

layer4567_start:
        ldr	q4, [x1], #0x10
        ldr	q6, [x3, #0x60]
        sqrdmulh	v8.8h, v27.8h, v4.h[5]
        mul	v19.8h, v27.8h, v4.h[4]
        ldr	q13, [x3, #0x50]
        mul	v14.8h, v1.8h, v4.h[2]
        mls	v19.8h, v8.8h, v7.h[0]
        sqrdmulh	v17.8h, v1.8h, v4.h[3]
        sub	v0.8h, v29.8h, v22.8h
        ldr	q16, [x3, #0x40]
        mls	v14.8h, v17.8h, v7.h[0]
        mul	v23.8h, v0.8h, v4.h[0]
        trn2	v24.4s, v16.4s, v13.4s
        trn1	v26.4s, v16.4s, v13.4s
        add	v18.8h, v14.8h, v19.8h
        sub	v10.8h, v14.8h, v19.8h
        sqrdmulh	v16.8h, v0.8h, v4.h[1]
        sqdmulh	v1.8h, v18.8h, v7.h[1]
        mul	v0.8h, v10.8h, v4.h[0]
        sqrdmulh	v12.8h, v10.8h, v4.h[1]
        mls	v23.8h, v16.8h, v7.h[0]
        srshr	v28.8h, v1.8h, #0xb
        ldr	q20, [x3, #0x70]
        ldr	q9, [x2, #0x30]
        trn2	v15.4s, v6.4s, v20.4s
        trn1	v13.4s, v6.4s, v20.4s
        str	q23, [x3, #0x20]
        trn2	v2.2d, v24.2d, v15.2d
        trn1	v3.2d, v24.2d, v15.2d
        trn1	v30.2d, v26.2d, v13.2d
        trn2	v27.2d, v26.2d, v13.2d
        sub	v15.8h, v30.8h, v3.8h
        mls	v18.8h, v28.8h, v7.h[0]
        sub	v26.8h, v27.8h, v2.8h
        sqrdmulh	v17.8h, v15.8h, v9.8h
        ldr	q8, [x2, #0x50]
        ldr	q14, [x2, #0x40]
        ldr	q11, [x2, #0x20]
        mul	v16.8h, v26.8h, v14.8h
        sqrdmulh	v26.8h, v26.8h, v8.8h
        mul	v8.8h, v15.8h, v11.8h
        add	v20.8h, v30.8h, v3.8h
        add	v3.8h, v27.8h, v2.8h
        mls	v16.8h, v26.8h, v7.h[0]
        mls	v8.8h, v17.8h, v7.h[0]
        ldr	q27, [x2], #0x60
        ldur	q9, [x2, #-0x50]
        sub	v10.8h, v8.8h, v16.8h
        sub	v6.8h, v20.8h, v3.8h
        add	v21.8h, v20.8h, v3.8h
        mul	v4.8h, v10.8h, v27.8h
        sqrdmulh	v20.8h, v6.8h, v9.8h
        sqrdmulh	v24.8h, v10.8h, v9.8h
        mul	v1.8h, v6.8h, v27.8h
        str	q18, [x3, #0x10]
        add	v10.8h, v8.8h, v16.8h
        mls	v4.8h, v24.8h, v7.h[0]
        mls	v1.8h, v20.8h, v7.h[0]
        trn1	v18.4s, v21.4s, v10.4s
        trn2	v16.4s, v21.4s, v10.4s
        mls	v0.8h, v12.8h, v7.h[0]
        trn2	v6.4s, v1.4s, v4.4s
        trn1	v8.4s, v1.4s, v4.4s
        add	v21.8h, v29.8h, v22.8h
        trn2	v25.2d, v16.2d, v6.2d
        trn1	v19.2d, v16.2d, v6.2d
        trn2	v13.2d, v18.2d, v8.2d
        trn1	v24.2d, v18.2d, v8.2d
        add	v22.8h, v13.8h, v25.8h
        add	v29.8h, v24.8h, v19.8h
        sub	v1.8h, v24.8h, v19.8h
        sqdmulh	v2.8h, v22.8h, v7.h[1]
        sqdmulh	v30.8h, v29.8h, v7.h[1]
        sub	v27.8h, v13.8h, v25.8h
        str	q0, [x3, #0x30]
        srshr	v0.8h, v2.8h, #0xb
        srshr	v17.8h, v30.8h, #0xb
        str	q21, [x3], #0x40
        mls	v22.8h, v0.8h, v7.h[0]
        mls	v29.8h, v17.8h, v7.h[0]
        sub	x4, x4, #0x1
        cbnz	x4, layer4567_start
        ldr	q4, [x1], #0x10
        sub	v5.8h, v29.8h, v22.8h
        add	v15.8h, v29.8h, v22.8h
        sqrdmulh	v21.8h, v1.8h, v4.h[3]
        mul	v1.8h, v1.8h, v4.h[2]
        sqrdmulh	v13.8h, v27.8h, v4.h[5]
        mul	v27.8h, v27.8h, v4.h[4]
        sqrdmulh	v6.8h, v5.8h, v4.h[1]
        mls	v1.8h, v21.8h, v7.h[0]
        str	q15, [x3], #0x40
        mls	v27.8h, v13.8h, v7.h[0]
        add	v22.8h, v1.8h, v27.8h
        sub	v12.8h, v1.8h, v27.8h
        mul	v1.8h, v5.8h, v4.h[0]
        sqdmulh	v3.8h, v22.8h, v7.h[1]
        sqrdmulh	v10.8h, v12.8h, v4.h[1]
        mul	v27.8h, v12.8h, v4.h[0]
        mls	v1.8h, v6.8h, v7.h[0]
        srshr	v13.8h, v3.8h, #0xb
        mls	v27.8h, v10.8h, v7.h[0]
        stur	q1, [x3, #-0x20]
        mls	v22.8h, v13.8h, v7.h[0]
        stur	q27, [x3, #-0x10]
        stur	q22, [x3, #-0x30]
        mov	x4, #0x4                // =4
        ldr	q0, [x1], #0x20
        ldur	q1, [x1, #-0x10]
        ldr	q12, [x0, #0xc0]
        ldr	q11, [x0, #0x80]
        ldr	q20, [x0, #0x40]
        sub	v6.8h, v11.8h, v12.8h
        add	v14.8h, v11.8h, v12.8h
        ldr	q21, [x0, #0x180]
        ldr	q15, [x0]
        mul	v8.8h, v6.8h, v1.h[0]
        sqrdmulh	v6.8h, v6.8h, v1.h[1]
        add	v28.8h, v15.8h, v20.8h
        sub	v4.8h, v15.8h, v20.8h
        ldr	q27, [x0, #0x1c0]
        ldr	q16, [x0, #0x100]
        add	v3.8h, v21.8h, v27.8h
        sub	v27.8h, v21.8h, v27.8h
        ldr	q19, [x0, #0x140]
        mls	v8.8h, v6.8h, v7.h[0]
        ldr	q5, [x0, #0x190]
        sub	v23.8h, v28.8h, v14.8h
        add	v24.8h, v28.8h, v14.8h
        ldr	q6, [x0, #0x150]
        mul	v26.8h, v4.8h, v0.h[6]
        sqrdmulh	v21.8h, v4.8h, v0.h[7]
        ldr	q4, [x0, #0x1d0]
        ldr	q18, [x0, #0x110]
        sub	v17.8h, v16.8h, v19.8h
        add	v9.8h, v16.8h, v19.8h
        mul	v10.8h, v27.8h, v1.h[4]
        sqrdmulh	v27.8h, v27.8h, v1.h[5]
        ldr	q16, [x0, #0x50]
        add	v25.8h, v9.8h, v3.8h
        sub	v13.8h, v9.8h, v3.8h
        mul	v9.8h, v17.8h, v1.h[2]
        sqrdmulh	v15.8h, v17.8h, v1.h[3]
        ldr	q11, [x0, #0x10]
        mls	v10.8h, v27.8h, v7.h[0]
        ldr	q19, [x0, #0xd0]
        ldr	q22, [x0, #0x90]
        mls	v26.8h, v21.8h, v7.h[0]
        sub	v29.8h, v18.8h, v6.8h
        mul	v20.8h, v23.8h, v0.h[2]
        sqrdmulh	v12.8h, v23.8h, v0.h[3]
        add	v17.8h, v26.8h, v8.8h
        sub	v21.8h, v26.8h, v8.8h
        sub	v31.8h, v24.8h, v25.8h
        add	v25.8h, v24.8h, v25.8h
        add	v28.8h, v18.8h, v6.8h
        sub	v6.8h, v5.8h, v4.8h
        add	v14.8h, v5.8h, v4.8h
        mls	v9.8h, v15.8h, v7.h[0]
        mul	v4.8h, v13.8h, v0.h[4]
        sqrdmulh	v26.8h, v13.8h, v0.h[5]
        sqrdmulh	v18.8h, v29.8h, v1.h[3]
        add	v24.8h, v22.8h, v19.8h
        add	v15.8h, v11.8h, v16.8h
        mul	v2.8h, v29.8h, v1.h[2]
        mls	v20.8h, v12.8h, v7.h[0]
        sub	v3.8h, v11.8h, v16.8h
        mls	v4.8h, v26.8h, v7.h[0]
        add	v16.8h, v9.8h, v10.8h
        sqrdmulh	v11.8h, v6.8h, v1.h[5]
        sub	v19.8h, v22.8h, v19.8h
        mul	v27.8h, v6.8h, v1.h[4]
        add	v30.8h, v15.8h, v24.8h
        sub	v29.8h, v28.8h, v14.8h
        sqrdmulh	v12.8h, v19.8h, v1.h[1]
        add	v22.8h, v28.8h, v14.8h
        sqrdmulh	v23.8h, v3.8h, v0.h[7]
        mul	v8.8h, v19.8h, v1.h[0]
        mls	v27.8h, v11.8h, v7.h[0]
        sub	v24.8h, v15.8h, v24.8h
        sub	v14.8h, v9.8h, v10.8h
        sub	v6.8h, v17.8h, v16.8h
        add	v10.8h, v17.8h, v16.8h
        sqrdmulh	v13.8h, v14.8h, v0.h[5]
        mul	v5.8h, v14.8h, v0.h[4]
        sqrdmulh	v9.8h, v21.8h, v0.h[3]
        mls	v2.8h, v18.8h, v7.h[0]
        add	v18.8h, v30.8h, v22.8h
        mul	v11.8h, v25.8h, v7.h[2]
        mul	v17.8h, v21.8h, v0.h[2]
        sqrdmulh	v15.8h, v24.8h, v0.h[3]
        mul	v16.8h, v29.8h, v0.h[4]
        sqrdmulh	v21.8h, v29.8h, v0.h[5]
        sub	v28.8h, v20.8h, v4.8h
        sqrdmulh	v19.8h, v25.8h, v7.h[3]
        mul	v25.8h, v24.8h, v0.h[2]
        mul	v26.8h, v3.8h, v0.h[6]
        mls	v5.8h, v13.8h, v7.h[0]
        mul	v29.8h, v28.8h, v0.h[0]
        mls	v17.8h, v9.8h, v7.h[0]
        sqrdmulh	v13.8h, v28.8h, v0.h[1]
        mul	v14.8h, v18.8h, v7.h[2]
        sqrdmulh	v24.8h, v6.8h, v1.h[7]
        sqrdmulh	v9.8h, v31.8h, v1.h[7]
        mls	v8.8h, v12.8h, v7.h[0]
        mul	v3.8h, v10.8h, v7.h[2]
        sqrdmulh	v28.8h, v18.8h, v7.h[3]
        sqrdmulh	v10.8h, v10.8h, v7.h[3]
        mls	v11.8h, v19.8h, v7.h[0]
        mul	v18.8h, v31.8h, v1.h[6]
        mls	v25.8h, v15.8h, v7.h[0]
        mul	v19.8h, v6.8h, v1.h[6]
        sub	v15.8h, v2.8h, v27.8h
        mls	v18.8h, v9.8h, v7.h[0]
        mls	v26.8h, v23.8h, v7.h[0]
        sqrdmulh	v31.8h, v15.8h, v0.h[5]
        mls	v3.8h, v10.8h, v7.h[0]
        mls	v16.8h, v21.8h, v7.h[0]
        mul	v23.8h, v15.8h, v0.h[4]
        mls	v19.8h, v24.8h, v7.h[0]
        str	q11, [x0], #0x10
        add	v21.8h, v2.8h, v27.8h
        add	v20.8h, v20.8h, v4.8h
        mls	v14.8h, v28.8h, v7.h[0]
        sub	v6.8h, v30.8h, v22.8h
        add	v9.8h, v25.8h, v16.8h
        sub	v10.8h, v17.8h, v5.8h
        str	q3, [x0, #0x30]
        add	v27.8h, v17.8h, v5.8h
        mls	v23.8h, v31.8h, v7.h[0]
        add	v15.8h, v26.8h, v8.8h
        str	q19, [x0, #0x130]
        mul	v4.8h, v6.8h, v1.h[6]
        str	q27, [x0, #0xb0]
        mls	v29.8h, v13.8h, v7.h[0]
        str	q20, [x0, #0x70]
        add	v27.8h, v15.8h, v21.8h
        sub	v12.8h, v15.8h, v21.8h
        str	q29, [x0, #0x170]
        sub	v3.8h, v25.8h, v16.8h
        str	q14, [x0], #0x10
        sqrdmulh	v5.8h, v10.8h, v0.h[1]
        str	q18, [x0, #0xe0]
        sub	x4, x4, #0x2

layer123_start:
        sub	v17.8h, v26.8h, v8.8h
        ldr	q28, [x0, #0xc0]
        sqrdmulh	v29.8h, v17.8h, v0.h[3]
        mul	v17.8h, v17.8h, v0.h[2]
        ldr	q8, [x0, #0x80]
        mul	v11.8h, v10.8h, v0.h[0]
        mls	v17.8h, v29.8h, v7.h[0]
        sub	v15.8h, v8.8h, v28.8h
        add	v20.8h, v8.8h, v28.8h
        ldr	q18, [x0]
        ldr	q16, [x0, #0x40]
        add	v25.8h, v17.8h, v23.8h
        ldr	q29, [x0, #0x140]
        ldr	q21, [x0, #0x180]
        sub	v10.8h, v17.8h, v23.8h
        ldr	q22, [x0, #0x100]
        sqrdmulh	v19.8h, v15.8h, v1.h[1]
        mul	v8.8h, v15.8h, v1.h[0]
        add	v14.8h, v18.8h, v16.8h
        sub	v30.8h, v18.8h, v16.8h
        sub	v23.8h, v22.8h, v29.8h
        sub	v24.8h, v14.8h, v20.8h
        add	v31.8h, v14.8h, v20.8h
        str	q25, [x0, #0xb0]
        mul	v26.8h, v30.8h, v0.h[6]
        mls	v11.8h, v5.8h, v7.h[0]
        add	v15.8h, v22.8h, v29.8h
        ldr	q25, [x0, #0x1c0]
        str	q11, [x0, #0x1a0]
        mul	v2.8h, v23.8h, v1.h[2]
        sqrdmulh	v13.8h, v23.8h, v1.h[3]
        sub	v5.8h, v21.8h, v25.8h
        add	v23.8h, v21.8h, v25.8h
        sqrdmulh	v16.8h, v30.8h, v0.h[7]
        mul	v11.8h, v5.8h, v1.h[4]
        mls	v8.8h, v19.8h, v7.h[0]
        sqrdmulh	v22.8h, v5.8h, v1.h[5]
        mls	v2.8h, v13.8h, v7.h[0]
        add	v13.8h, v15.8h, v23.8h
        mls	v26.8h, v16.8h, v7.h[0]
        mls	v11.8h, v22.8h, v7.h[0]
        sqrdmulh	v19.8h, v6.8h, v1.h[7]
        sqrdmulh	v14.8h, v12.8h, v1.h[7]
        add	v28.8h, v26.8h, v8.8h
        sqrdmulh	v5.8h, v10.8h, v0.h[1]
        sub	v18.8h, v2.8h, v11.8h
        mls	v4.8h, v19.8h, v7.h[0]
        sqrdmulh	v19.8h, v3.8h, v0.h[1]
        mul	v17.8h, v24.8h, v0.h[2]
        sqrdmulh	v22.8h, v24.8h, v0.h[3]
        add	v30.8h, v31.8h, v13.8h
        sub	v6.8h, v31.8h, v13.8h
        sqrdmulh	v16.8h, v18.8h, v0.h[5]
        sqrdmulh	v21.8h, v30.8h, v7.h[3]
        mls	v17.8h, v22.8h, v7.h[0]
        add	v2.8h, v2.8h, v11.8h
        mul	v11.8h, v12.8h, v1.h[6]
        mul	v29.8h, v30.8h, v7.h[2]
        sub	v12.8h, v28.8h, v2.8h
        sub	v24.8h, v15.8h, v23.8h
        mls	v11.8h, v14.8h, v7.h[0]
        mls	v29.8h, v21.8h, v7.h[0]
        sqrdmulh	v22.8h, v27.8h, v7.h[3]
        mul	v23.8h, v3.8h, v0.h[0]
        mul	v14.8h, v27.8h, v7.h[2]
        str	q29, [x0], #0x10
        sqrdmulh	v29.8h, v24.8h, v0.h[5]
        str	q4, [x0, #0xe0]
        add	v27.8h, v28.8h, v2.8h
        mls	v23.8h, v19.8h, v7.h[0]
        str	q11, [x0, #0x120]
        mls	v14.8h, v22.8h, v7.h[0]
        mul	v11.8h, v24.8h, v0.h[4]
        str	q23, [x0, #0x160]
        mul	v23.8h, v18.8h, v0.h[4]
        str	q14, [x0, #0x20]
        mls	v11.8h, v29.8h, v7.h[0]
        str	q9, [x0, #0x60]
        mls	v23.8h, v16.8h, v7.h[0]
        mul	v4.8h, v6.8h, v1.h[6]
        add	v9.8h, v17.8h, v11.8h
        sub	v3.8h, v17.8h, v11.8h
        sub	x4, x4, #0x1
        cbnz	x4, layer123_start
        mul	v18.8h, v27.8h, v7.h[2]
        sub	v11.8h, v26.8h, v8.8h
        sqrdmulh	v2.8h, v3.8h, v0.h[1]
        mul	v17.8h, v3.8h, v0.h[0]
        mul	v3.8h, v10.8h, v0.h[0]
        sqrdmulh	v8.8h, v6.8h, v1.h[7]
        mul	v6.8h, v11.8h, v0.h[2]
        mul	v10.8h, v12.8h, v1.h[6]
        sqrdmulh	v26.8h, v11.8h, v0.h[3]
        sqrdmulh	v19.8h, v12.8h, v1.h[7]
        mls	v3.8h, v5.8h, v7.h[0]
        mls	v4.8h, v8.8h, v7.h[0]
        mls	v6.8h, v26.8h, v7.h[0]
        str	q9, [x0, #0x70]
        mls	v17.8h, v2.8h, v7.h[0]
        sqrdmulh	v27.8h, v27.8h, v7.h[3]
        sub	v8.8h, v6.8h, v23.8h
        str	q3, [x0, #0x1a0]
        mls	v10.8h, v19.8h, v7.h[0]
        str	q17, [x0, #0x170]
        sqrdmulh	v17.8h, v8.8h, v0.h[1]
        str	q4, [x0, #0xf0]
        add	v3.8h, v6.8h, v23.8h
        mul	v4.8h, v8.8h, v0.h[0]
        str	q10, [x0, #0x130]
        mls	v18.8h, v27.8h, v7.h[0]
        str	q3, [x0, #0xb0]
        mls	v4.8h, v17.8h, v7.h[0]
        str	q18, [x0, #0x30]
        str	q4, [x0, #0x1b0]
        ldp	d8, d9, [sp]
        ldp	d10, d11, [sp, #0x10]
        ldp	d12, d13, [sp, #0x20]
        ldp	d14, d15, [sp, #0x30]
        add	sp, sp, #0x40
        ret

#endif /* MLK_ARITH_BACKEND_AARCH64 &&
          !MLK_MULTILEVEL_BUILD_NO_SHARED */
