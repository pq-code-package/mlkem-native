/*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */

#include "../../../common.h"
#if defined(MLK_ARITH_BACKEND_AARCH64) &&  !defined(MLK_CONFIG_MULTILEVEL_NO_SHARED)

/*
 * WARNING: This file is auto-derived from the mlkem-native source file
 *   dev/aarch64_opt/src/poly_tobytes_asm.S using scripts/simpasm. Do not modify it directly.
 */


.text
.balign 4
.global MLK_ASM_NAMESPACE(poly_tobytes_asm)
MLK_ASM_FN_SYMBOL(poly_tobytes_asm)

        mov	x2, #0x10               // =16
        ldr	q29, [x1], #0x20
        ldur	q31, [x1, #-0x10]
        ldr	q18, [x1, #0x10]
        ldr	q23, [x1], #0x20
        ldr	q22, [x1, #0x50]
        ldr	q17, [x1, #0x10]
        ldr	q1, [x1, #0x30]
        uzp1	v5.8h, v29.8h, v31.8h
        uzp2	v20.8h, v29.8h, v31.8h
        ldr	q31, [x1], #0x20
        uzp2	v21.8h, v23.8h, v18.8h
        xtn	v29.8b, v20.8h
        shrn	v26.8b, v5.8h, #0x8
        xtn	v25.8b, v5.8h
        ldr	q28, [x1], #0x20
        sli	v26.8b, v29.8b, #0x4
        lsr	x2, x2, #2
        sub	x2, x2, #0x2

poly_tobytes_loop_start:
        ldr	q30, [x1], #0x20
        uzp1	v3.8h, v23.8h, v18.8h
        ldr	q18, [x1, #0x10]
        uzp2	v16.8h, v28.8h, v1.8h
        shrn	v27.8b, v20.8h, #0x4
        uzp1	v5.8h, v28.8h, v1.8h
        shrn	v23.8b, v3.8h, #0x8
        uzp2	v0.8h, v31.8h, v17.8h
        uzp1	v31.8h, v31.8h, v17.8h
        uzp2	v20.8h, v30.8h, v22.8h
        shrn	v6.8b, v16.8h, #0x4
        xtn	v7.8b, v0.8h
        st3	{ v25.8b, v26.8b, v27.8b }, [x0], #24
        shrn	v24.8b, v21.8h, #0x4
        shrn	v28.8b, v31.8h, #0x8
        ldr	q1, [x1, #0x50]
        shrn	v29.8b, v0.8h, #0x4
        ldr	q17, [x1, #0x30]
        xtn	v4.8b, v5.8h
        xtn	v19.8b, v21.8h
        uzp1	v2.8h, v30.8h, v22.8h
        shrn	v5.8b, v5.8h, #0x8
        sli	v23.8b, v19.8b, #0x4
        xtn	v22.8b, v3.8h
        sli	v28.8b, v7.8b, #0x4
        xtn	v3.8b, v20.8h
        shrn	v26.8b, v2.8h, #0x8
        xtn	v25.8b, v2.8h
        xtn	v27.8b, v31.8h
        st3	{ v22.8b, v23.8b, v24.8b }, [x0], #24
        xtn	v16.8b, v16.8h
        ldr	q23, [x1], #0x20
        ldr	q31, [x1], #0x20
        st3	{ v27.8b, v28.8b, v29.8b }, [x0], #24
        sli	v5.8b, v16.8b, #0x4
        ldr	q28, [x1], #0x20
        sli	v26.8b, v3.8b, #0x4
        ldr	q22, [x1, #0x10]
        uzp2	v21.8h, v23.8h, v18.8h
        st3	{ v4.8b, v5.8b, v6.8b }, [x0], #24
        subs	x2, x2, #0x1
        cbnz	x2, poly_tobytes_loop_start
        uzp2	v2.8h, v28.8h, v1.8h
        uzp1	v0.8h, v28.8h, v1.8h
        shrn	v27.8b, v20.8h, #0x4
        uzp1	v18.8h, v23.8h, v18.8h
        shrn	v5.8b, v0.8h, #0x8
        xtn	v29.8b, v2.8h
        st3	{ v25.8b, v26.8b, v27.8b }, [x0], #24
        shrn	v6.8b, v2.8h, #0x4
        ldr	q25, [x1], #0x20
        uzp1	v24.8h, v31.8h, v17.8h
        uzp2	v16.8h, v31.8h, v17.8h
        ldr	q23, [x1], #0x20
        xtn	v28.8b, v21.8h
        shrn	v21.8b, v21.8h, #0x4
        xtn	v2.8b, v16.8h
        shrn	v20.8b, v18.8h, #0x8
        sli	v5.8b, v29.8b, #0x4
        xtn	v4.8b, v0.8h
        sli	v20.8b, v28.8b, #0x4
        xtn	v19.8b, v18.8h
        shrn	v18.8b, v24.8h, #0x8
        xtn	v17.8b, v24.8h
        st3	{ v19.8b, v20.8b, v21.8b }, [x0], #24
        shrn	v19.8b, v16.8h, #0x4
        uzp1	v27.8h, v25.8h, v22.8h
        ldr	q1, [x1, #0x10]
        sli	v18.8b, v2.8b, #0x4
        ldur	q21, [x1, #-0x10]
        xtn	v26.8b, v27.8h
        shrn	v27.8b, v27.8h, #0x8
        st3	{ v17.8b, v18.8b, v19.8b }, [x0], #24
        uzp2	v29.8h, v25.8h, v22.8h
        ldr	q20, [x1], #0x20
        st3	{ v4.8b, v5.8b, v6.8b }, [x0], #24
        ldr	q31, [x1], #0x20
        ldur	q3, [x1, #-0x10]
        uzp1	v7.8h, v23.8h, v21.8h
        shrn	v28.8b, v29.8h, #0x4
        uzp2	v25.8h, v23.8h, v21.8h
        uzp1	v16.8h, v20.8h, v1.8h
        uzp2	v4.8h, v20.8h, v1.8h
        uzp2	v0.8h, v31.8h, v3.8h
        uzp1	v18.8h, v31.8h, v3.8h
        shrn	v22.8b, v16.8h, #0x8
        xtn	v21.8b, v16.8h
        xtn	v1.8b, v0.8h
        xtn	v19.8b, v4.8h
        xtn	v2.8b, v29.8h
        shrn	v6.8b, v7.8h, #0x8
        sli	v22.8b, v19.8b, #0x4
        xtn	v30.8b, v25.8h
        xtn	v5.8b, v7.8h
        sli	v27.8b, v2.8b, #0x4
        sli	v6.8b, v30.8b, #0x4
        xtn	v16.8b, v18.8h
        shrn	v7.8b, v25.8h, #0x4
        st3	{ v26.8b, v27.8b, v28.8b }, [x0], #24
        shrn	v23.8b, v4.8h, #0x4
        shrn	v17.8b, v18.8h, #0x8
        st3	{ v5.8b, v6.8b, v7.8b }, [x0], #24
        shrn	v18.8b, v0.8h, #0x4
        sli	v17.8b, v1.8b, #0x4
        st3	{ v21.8b, v22.8b, v23.8b }, [x0], #24
        st3	{ v16.8b, v17.8b, v18.8b }, [x0], #24
        ret

#endif /* MLK_ARITH_BACKEND_AARCH64 && !MLK_CONFIG_MULTILEVEL_NO_SHARED */
