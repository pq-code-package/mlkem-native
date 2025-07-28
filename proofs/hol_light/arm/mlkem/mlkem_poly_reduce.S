/*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */


/*
 * WARNING: This file is auto-derived from the mlkem-native source file
 *   dev/aarch64_opt/src/poly_reduce_asm.S using scripts/simpasm. Do not modify it directly.
 */


.text
.balign 4
#ifdef __APPLE__
.global _PQCP_MLKEM_NATIVE_MLKEM768_poly_reduce_asm
_PQCP_MLKEM_NATIVE_MLKEM768_poly_reduce_asm:
#else
.global PQCP_MLKEM_NATIVE_MLKEM768_poly_reduce_asm
PQCP_MLKEM_NATIVE_MLKEM768_poly_reduce_asm:
#endif

        mov	w2, #0xd01              // =3329
        dup	v3.8h, w2
        mov	w2, #0x4ebf             // =20159
        dup	v4.8h, w2
        mov	x1, #0x8                // =8
        ldr	q0, [x0, #0x30]
        ldr	q17, [x0, #0x10]
        ldr	q26, [x0], #0x40
        ldur	q18, [x0, #-0x20]
        ldr	q5, [x0, #0x30]
        sqdmulh	v22.8h, v0.8h, v4.h[0]
        sqdmulh	v29.8h, v17.8h, v4.h[0]
        sqdmulh	v16.8h, v26.8h, v4.h[0]
        srshr	v22.8h, v22.8h, #0xb
        sqdmulh	v2.8h, v18.8h, v4.h[0]
        srshr	v25.8h, v29.8h, #0xb
        mls	v0.8h, v22.8h, v3.h[0]
        srshr	v16.8h, v16.8h, #0xb
        mls	v17.8h, v25.8h, v3.h[0]
        srshr	v27.8h, v2.8h, #0xb
        mls	v26.8h, v16.8h, v3.h[0]
        sshr	v28.8h, v0.8h, #0xf
        mls	v18.8h, v27.8h, v3.h[0]
        sshr	v16.8h, v17.8h, #0xf
        and	v20.16b, v3.16b, v28.16b
        and	v22.16b, v3.16b, v16.16b
        sshr	v28.8h, v26.8h, #0xf
        add	v16.8h, v0.8h, v20.8h
        add	v25.8h, v17.8h, v22.8h
        and	v27.16b, v3.16b, v28.16b
        sub	x1, x1, #0x2

poly_reduce_loop_start:
        ldr	q0, [x0, #0x10]
        sshr	v21.8h, v18.8h, #0xf
        add	v17.8h, v26.8h, v27.8h
        ldr	q26, [x0], #0x40
        and	v21.16b, v3.16b, v21.16b
        sqdmulh	v19.8h, v5.8h, v4.h[0]
        stur	q17, [x0, #-0x80]
        sqdmulh	v7.8h, v0.8h, v4.h[0]
        add	v21.8h, v18.8h, v21.8h
        stur	q25, [x0, #-0x70]
        ldur	q18, [x0, #-0x20]
        stur	q21, [x0, #-0x60]
        sqdmulh	v2.8h, v26.8h, v4.h[0]
        srshr	v29.8h, v19.8h, #0xb
        stur	q16, [x0, #-0x50]
        srshr	v1.8h, v7.8h, #0xb
        sqdmulh	v30.8h, v18.8h, v4.h[0]
        srshr	v23.8h, v2.8h, #0xb
        mls	v5.8h, v29.8h, v3.h[0]
        mls	v0.8h, v1.8h, v3.h[0]
        srshr	v6.8h, v30.8h, #0xb
        mls	v26.8h, v23.8h, v3.h[0]
        sshr	v28.8h, v5.8h, #0xf
        sshr	v20.8h, v0.8h, #0xf
        mls	v18.8h, v6.8h, v3.h[0]
        and	v22.16b, v3.16b, v28.16b
        sshr	v24.8h, v26.8h, #0xf
        and	v31.16b, v3.16b, v20.16b
        add	v16.8h, v5.8h, v22.8h
        ldr	q5, [x0, #0x30]
        and	v27.16b, v3.16b, v24.16b
        add	v25.8h, v0.8h, v31.8h
        subs	x1, x1, #0x1
        cbnz	x1, poly_reduce_loop_start
        ldr	q0, [x0, #0x10]
        ldr	q29, [x0], #0x40
        stur	q25, [x0, #-0x70]
        sqdmulh	v25.8h, v5.8h, v4.h[0]
        add	v17.8h, v26.8h, v27.8h
        ldur	q27, [x0, #-0x20]
        stur	q16, [x0, #-0x50]
        stur	q17, [x0, #-0x80]
        sqdmulh	v31.8h, v0.8h, v4.h[0]
        srshr	v7.8h, v25.8h, #0xb
        sqdmulh	v25.8h, v27.8h, v4.h[0]
        sqdmulh	v6.8h, v29.8h, v4.h[0]
        srshr	v21.8h, v31.8h, #0xb
        mls	v5.8h, v7.8h, v3.h[0]
        srshr	v25.8h, v25.8h, #0xb
        mls	v0.8h, v21.8h, v3.h[0]
        srshr	v21.8h, v6.8h, #0xb
        mls	v27.8h, v25.8h, v3.h[0]
        mls	v29.8h, v21.8h, v3.h[0]
        sshr	v25.8h, v5.8h, #0xf
        sshr	v16.8h, v0.8h, #0xf
        and	v30.16b, v3.16b, v25.16b
        sshr	v25.8h, v18.8h, #0xf
        and	v21.16b, v3.16b, v16.16b
        sshr	v31.8h, v27.8h, #0xf
        and	v25.16b, v3.16b, v25.16b
        and	v1.16b, v3.16b, v31.16b
        sshr	v6.8h, v29.8h, #0xf
        add	v21.8h, v0.8h, v21.8h
        add	v25.8h, v18.8h, v25.8h
        add	v2.8h, v5.8h, v30.8h
        and	v6.16b, v3.16b, v6.16b
        stur	q21, [x0, #-0x30]
        add	v21.8h, v27.8h, v1.8h
        add	v27.8h, v29.8h, v6.8h
        stur	q2, [x0, #-0x10]
        stur	q25, [x0, #-0x60]
        stur	q21, [x0, #-0x20]
        stur	q27, [x0, #-0x40]
        ret
