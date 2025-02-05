/*
 * Copyright (c) 2024-2025 The mlkem-native project authors
 * Copyright (c) 2021-2022 Arm Limited
 * Copyright (c) 2022 Matthias Kannwischer
 * SPDX-License-Identifier: MIT
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
 * SOFTWARE.
 *
 */

//
// Author: Hanno Becker <hanno.becker@arm.com>
// Author: Matthias Kannwischer <matthias@kannwischer.eu>
//
// This implementation is essentially from the paper
//
//   Hybrid scalar/vector implementations of Keccak and SPHINCS+ on AArch64
//   https://eprint.iacr.org/2022/1243
//
// The only difference is interleaving/deinterleaving of Keccak state
// during load and store, so that the caller need not do this.
//

#include "../../../../common.h"
#if (defined(MLKEM_NATIVE_FIPS202_BACKEND_AARCH64_DEFAULT) || \
     defined(MLKEM_NATIVE_FIPS202_BACKEND_AARCH64_A55)) &&    \
    !defined(MLKEM_NATIVE_MULTILEVEL_BUILD_NO_SHARED)

#if defined(__ARM_FEATURE_SHA3)

/*
 * WARNING: This file is auto-derived from the mlkem-native source file
 *   dev/fips202/aarch64/src/keccak_f1600_x2_v8a_v84a_asm_hybrid.S using scripts/simpasm. Do not modify it directly.
 */


.text
.balign 4
.global MLKEM_ASM_NAMESPACE(keccak_f1600_x2_v8a_v84a_asm_hybrid)
MLKEM_ASM_NAMESPACE(keccak_f1600_x2_v8a_v84a_asm_hybrid):

        sub	sp, sp, #0xa0
        stp	x19, x20, [sp, #0x40]
        stp	x21, x22, [sp, #0x50]
        stp	x23, x24, [sp, #0x60]
        stp	x25, x26, [sp, #0x70]
        stp	x27, x28, [sp, #0x80]
        stp	x29, x30, [sp, #0x90]
        stp	d8, d9, [sp]
        stp	d10, d11, [sp, #0x10]
        stp	d12, d13, [sp, #0x20]
        stp	d14, d15, [sp, #0x30]
        mov	x1, x1
        ld2	{ v0.d, v1.d }[0], [x0], #16
        ld2	{ v2.d, v3.d }[0], [x0], #16
        ld2	{ v4.d, v5.d }[0], [x0], #16
        ld2	{ v6.d, v7.d }[0], [x0], #16
        ld2	{ v8.d, v9.d }[0], [x0], #16
        ld2	{ v10.d, v11.d }[0], [x0], #16
        ld2	{ v12.d, v13.d }[0], [x0], #16
        ld2	{ v14.d, v15.d }[0], [x0], #16
        ld2	{ v16.d, v17.d }[0], [x0], #16
        ld2	{ v18.d, v19.d }[0], [x0], #16
        ld2	{ v20.d, v21.d }[0], [x0], #16
        ld2	{ v22.d, v23.d }[0], [x0], #16
        ld1	{ v24.d }[0], [x0], #8
        ld2	{ v0.d, v1.d }[1], [x0], #16
        ld2	{ v2.d, v3.d }[1], [x0], #16
        ld2	{ v4.d, v5.d }[1], [x0], #16
        ld2	{ v6.d, v7.d }[1], [x0], #16
        ld2	{ v8.d, v9.d }[1], [x0], #16
        ld2	{ v10.d, v11.d }[1], [x0], #16
        ld2	{ v12.d, v13.d }[1], [x0], #16
        ld2	{ v14.d, v15.d }[1], [x0], #16
        ld2	{ v16.d, v17.d }[1], [x0], #16
        ld2	{ v18.d, v19.d }[1], [x0], #16
        ld2	{ v20.d, v21.d }[1], [x0], #16
        ld2	{ v22.d, v23.d }[1], [x0], #16
        ld1	{ v24.d }[1], [x0], #8
        sub	x0, x0, #0x190
        mov	x2, #0x18               // =24

keccak_f1600_x2_v8a_v84a_loop:
        eor	v30.16b, v0.16b, v5.16b
        eor	v30.16b, v30.16b, v10.16b
        eor3	v30.16b, v30.16b, v15.16b, v20.16b
        eor	v29.16b, v1.16b, v6.16b
        eor	v29.16b, v29.16b, v11.16b
        eor3	v29.16b, v29.16b, v16.16b, v21.16b
        eor	v28.16b, v2.16b, v7.16b
        eor	v28.16b, v28.16b, v12.16b
        eor3	v28.16b, v28.16b, v17.16b, v22.16b
        eor	v27.16b, v3.16b, v8.16b
        eor	v27.16b, v27.16b, v13.16b
        eor3	v27.16b, v27.16b, v18.16b, v23.16b
        eor	v26.16b, v4.16b, v9.16b
        eor	v26.16b, v26.16b, v14.16b
        eor3	v26.16b, v26.16b, v19.16b, v24.16b
        add	v31.2d, v28.2d, v28.2d
        sri	v31.2d, v28.2d, #0x3f
        eor	v25.16b, v31.16b, v30.16b
        rax1	v28.2d, v28.2d, v26.2d
        add	v31.2d, v29.2d, v29.2d
        sri	v31.2d, v29.2d, #0x3f
        eor	v26.16b, v31.16b, v26.16b
        rax1	v29.2d, v29.2d, v27.2d
        add	v31.2d, v30.2d, v30.2d
        sri	v31.2d, v30.2d, #0x3f
        eor	v27.16b, v31.16b, v27.16b
        eor	v30.16b, v0.16b, v26.16b
        xar	v0.2d, v2.2d, v29.2d, #0x2
        eor	v31.16b, v12.16b, v29.16b
        shl	v2.2d, v31.2d, #0x2b
        sri	v2.2d, v31.2d, #0x15
        xar	v12.2d, v13.2d, v28.2d, #0x27
        eor	v31.16b, v19.16b, v27.16b
        shl	v13.2d, v31.2d, #0x8
        sri	v13.2d, v31.2d, #0x38
        xar	v19.2d, v23.2d, v28.2d, #0x8
        eor	v31.16b, v15.16b, v26.16b
        shl	v23.2d, v31.2d, #0x29
        sri	v23.2d, v31.2d, #0x17
        xar	v15.2d, v1.2d, v25.2d, #0x3f
        eor	v31.16b, v8.16b, v28.16b
        shl	v1.2d, v31.2d, #0x37
        sri	v1.2d, v31.2d, #0x9
        xar	v8.2d, v16.2d, v25.2d, #0x13
        eor	v31.16b, v7.16b, v29.16b
        shl	v16.2d, v31.2d, #0x6
        sri	v16.2d, v31.2d, #0x3a
        xar	v7.2d, v10.2d, v26.2d, #0x3d
        eor	v31.16b, v3.16b, v28.16b
        shl	v10.2d, v31.2d, #0x1c
        sri	v10.2d, v31.2d, #0x24
        xar	v3.2d, v18.2d, v28.2d, #0x2b
        eor	v31.16b, v17.16b, v29.16b
        shl	v18.2d, v31.2d, #0xf
        sri	v18.2d, v31.2d, #0x31
        xar	v17.2d, v11.2d, v25.2d, #0x36
        eor	v31.16b, v9.16b, v27.16b
        shl	v11.2d, v31.2d, #0x14
        sri	v11.2d, v31.2d, #0x2c
        xar	v9.2d, v22.2d, v29.2d, #0x3
        eor	v31.16b, v14.16b, v27.16b
        shl	v22.2d, v31.2d, #0x27
        sri	v22.2d, v31.2d, #0x19
        xar	v14.2d, v20.2d, v26.2d, #0x2e
        eor	v31.16b, v4.16b, v27.16b
        shl	v20.2d, v31.2d, #0x1b
        sri	v20.2d, v31.2d, #0x25
        xar	v4.2d, v24.2d, v27.2d, #0x32
        eor	v31.16b, v21.16b, v25.16b
        shl	v24.2d, v31.2d, #0x2
        sri	v24.2d, v31.2d, #0x3e
        xar	v21.2d, v5.2d, v26.2d, #0x1c
        eor	v31.16b, v6.16b, v25.16b
        shl	v27.2d, v31.2d, #0x2c
        sri	v27.2d, v31.2d, #0x14
        ld1r	{ v28.2d }, [x1], #8
        bcax	v5.16b, v10.16b, v7.16b, v11.16b
        bic	v31.16b, v8.16b, v7.16b
        eor	v6.16b, v31.16b, v11.16b
        bcax	v7.16b, v7.16b, v9.16b, v8.16b
        bic	v31.16b, v10.16b, v9.16b
        eor	v8.16b, v31.16b, v8.16b
        bcax	v9.16b, v9.16b, v11.16b, v10.16b
        bic	v31.16b, v12.16b, v16.16b
        eor	v10.16b, v31.16b, v15.16b
        bcax	v11.16b, v16.16b, v13.16b, v12.16b
        bic	v31.16b, v14.16b, v13.16b
        eor	v12.16b, v31.16b, v12.16b
        bcax	v13.16b, v13.16b, v15.16b, v14.16b
        bic	v31.16b, v16.16b, v15.16b
        eor	v14.16b, v31.16b, v14.16b
        bcax	v15.16b, v20.16b, v17.16b, v21.16b
        bic	v31.16b, v18.16b, v17.16b
        eor	v16.16b, v31.16b, v21.16b
        bcax	v17.16b, v17.16b, v19.16b, v18.16b
        bic	v31.16b, v20.16b, v19.16b
        eor	v18.16b, v31.16b, v18.16b
        bcax	v19.16b, v19.16b, v21.16b, v20.16b
        bic	v31.16b, v22.16b, v1.16b
        eor	v20.16b, v31.16b, v0.16b
        bcax	v21.16b, v1.16b, v23.16b, v22.16b
        bic	v31.16b, v24.16b, v23.16b
        eor	v22.16b, v31.16b, v22.16b
        bcax	v23.16b, v23.16b, v0.16b, v24.16b
        bic	v31.16b, v1.16b, v0.16b
        eor	v24.16b, v31.16b, v24.16b
        bcax	v0.16b, v30.16b, v2.16b, v27.16b
        bic	v31.16b, v3.16b, v2.16b
        eor	v1.16b, v31.16b, v27.16b
        bcax	v2.16b, v2.16b, v4.16b, v3.16b
        bic	v31.16b, v30.16b, v4.16b
        eor	v3.16b, v31.16b, v3.16b
        bcax	v4.16b, v4.16b, v27.16b, v30.16b
        eor	v0.16b, v0.16b, v28.16b
        sub	x2, x2, #0x1
        cbnz	x2, keccak_f1600_x2_v8a_v84a_loop
        st2	{ v0.d, v1.d }[0], [x0], #16
        st2	{ v2.d, v3.d }[0], [x0], #16
        st2	{ v4.d, v5.d }[0], [x0], #16
        st2	{ v6.d, v7.d }[0], [x0], #16
        st2	{ v8.d, v9.d }[0], [x0], #16
        st2	{ v10.d, v11.d }[0], [x0], #16
        st2	{ v12.d, v13.d }[0], [x0], #16
        st2	{ v14.d, v15.d }[0], [x0], #16
        st2	{ v16.d, v17.d }[0], [x0], #16
        st2	{ v18.d, v19.d }[0], [x0], #16
        st2	{ v20.d, v21.d }[0], [x0], #16
        st2	{ v22.d, v23.d }[0], [x0], #16
        st1	{ v24.d }[0], [x0], #8
        st2	{ v0.d, v1.d }[1], [x0], #16
        st2	{ v2.d, v3.d }[1], [x0], #16
        st2	{ v4.d, v5.d }[1], [x0], #16
        st2	{ v6.d, v7.d }[1], [x0], #16
        st2	{ v8.d, v9.d }[1], [x0], #16
        st2	{ v10.d, v11.d }[1], [x0], #16
        st2	{ v12.d, v13.d }[1], [x0], #16
        st2	{ v14.d, v15.d }[1], [x0], #16
        st2	{ v16.d, v17.d }[1], [x0], #16
        st2	{ v18.d, v19.d }[1], [x0], #16
        st2	{ v20.d, v21.d }[1], [x0], #16
        st2	{ v22.d, v23.d }[1], [x0], #16
        st1	{ v24.d }[1], [x0], #8
        ldp	d8, d9, [sp]
        ldp	d10, d11, [sp, #0x10]
        ldp	d12, d13, [sp, #0x20]
        ldp	d14, d15, [sp, #0x30]
        ldp	x19, x20, [sp, #0x40]
        ldp	x21, x22, [sp, #0x50]
        ldp	x23, x24, [sp, #0x60]
        ldp	x25, x26, [sp, #0x70]
        ldp	x27, x28, [sp, #0x80]
        ldp	x29, x30, [sp, #0x90]
        add	sp, sp, #0xa0
        ret

#endif /* __ARM_FEATURE_SHA3 */

#endif /* (defined(MLKEM_NATIVE_FIPS202_BACKEND_AARCH64_DEFAULT) ||
          defined(MLKEM_NATIVE_FIPS202_BACKEND_AARCH64_A55) &&
         !defined(MLKEM_NATIVE_MULTILEVEL_BUILD_NO_SHARED)*/
