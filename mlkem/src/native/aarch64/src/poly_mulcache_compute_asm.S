/*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */

#include "../../../common.h"
#if defined(MLK_ARITH_BACKEND_AARCH64) &&  !defined(MLK_CONFIG_MULTILEVEL_NO_SHARED)

/*
 * WARNING: This file is auto-derived from the mlkem-native source file
 *   dev/aarch64_opt/src/poly_mulcache_compute_asm.S using scripts/simpasm. Do not modify it directly.
 */


.text
.balign 4
.global MLK_ASM_NAMESPACE(poly_mulcache_compute_asm)
MLK_ASM_FN_SYMBOL(poly_mulcache_compute_asm)

        mov	w5, #0xd01              // =3329
        dup	v6.8h, w5
        mov	w5, #0x4ebf             // =20159
        dup	v7.8h, w5
        mov	x4, #0x10               // =16
        ldr	q18, [x1], #0x20
        ldur	q0, [x1, #-0x10]
        ldr	q4, [x3], #0x10
        ldr	q26, [x2], #0x10
        ldr	q29, [x1, #0x10]
        ldr	q5, [x1], #0x20
        uzp2	v17.8h, v18.8h, v0.8h
        ldr	q18, [x3], #0x10
        sqrdmulh	v0.8h, v17.8h, v4.8h
        mul	v26.8h, v17.8h, v26.8h
        sub	x4, x4, #0x2

poly_mulcache_compute_loop_start:
        uzp2	v17.8h, v5.8h, v29.8h
        mls	v26.8h, v0.8h, v6.h[0]
        ldr	q16, [x2], #0x10
        ldr	q5, [x1], #0x20
        sqrdmulh	v0.8h, v17.8h, v18.8h
        ldur	q29, [x1, #-0x10]
        ldr	q18, [x3], #0x10
        str	q26, [x0], #0x10
        mul	v26.8h, v17.8h, v16.8h
        subs	x4, x4, #0x1
        cbnz	x4, poly_mulcache_compute_loop_start
        mls	v26.8h, v0.8h, v6.h[0]
        uzp2	v16.8h, v5.8h, v29.8h
        ldr	q4, [x2], #0x10
        sqrdmulh	v2.8h, v16.8h, v18.8h
        str	q26, [x0], #0x10
        mul	v29.8h, v16.8h, v4.8h
        mls	v29.8h, v2.8h, v6.h[0]
        str	q29, [x0], #0x10
        ret

#endif /* MLK_ARITH_BACKEND_AARCH64 && !MLK_CONFIG_MULTILEVEL_NO_SHARED */
