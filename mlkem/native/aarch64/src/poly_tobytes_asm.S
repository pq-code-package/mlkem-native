/*
 * Copyright (c) 2024-2025 The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0
 */

#include "../../../common.h"
#if defined(MLK_ARITH_BACKEND_AARCH64) &&  !defined(MLK_MULTILEVEL_BUILD_NO_SHARED)

/*
 * WARNING: This file is auto-derived from the mlkem-native source file
 *   dev/aarch64_opt/src/poly_tobytes_asm.S using scripts/simpasm. Do not modify it directly.
 */


.text
.balign 4
.global MLK_ASM_NAMESPACE(poly_tobytes_asm)
MLK_ASM_FN_SYMBOL(poly_tobytes_asm)

        mov	x2, #0x10               // =16
        lsr	x2, x2, #2

poly_tobytes_asm_asm_loop_start:
        ld2	{ v25.8h, v26.8h }, [x1], #32
        ld2	{ v16.8h, v17.8h }, [x1], #32
        shrn	v24.8b, v25.8h, #0x8
        shrn	v18.8b, v17.8h, #0x4
        xtn	v21.8b, v17.8h
        shrn	v17.8b, v16.8h, #0x8
        xtn	v16.8b, v16.8h
        xtn	v23.8b, v25.8h
        xtn	v29.8b, v26.8h
        shrn	v25.8b, v26.8h, #0x4
        sli	v24.8b, v29.8b, #0x4
        sli	v17.8b, v21.8b, #0x4
        st3	{ v23.8b, v24.8b, v25.8b }, [x0], #24
        st3	{ v16.8b, v17.8b, v18.8b }, [x0], #24
        ld2	{ v2.8h, v3.8h }, [x1], #32
        ld2	{ v27.8h, v28.8h }, [x1], #32
        xtn	v16.8b, v3.8h
        shrn	v17.8b, v2.8h, #0x8
        sli	v17.8b, v16.8b, #0x4
        xtn	v16.8b, v2.8h
        shrn	v18.8b, v3.8h, #0x4
        st3	{ v16.8b, v17.8b, v18.8b }, [x0], #24
        xtn	v16.8b, v28.8h
        shrn	v17.8b, v27.8h, #0x8
        sli	v17.8b, v16.8b, #0x4
        xtn	v16.8b, v27.8h
        shrn	v18.8b, v28.8h, #0x4
        st3	{ v16.8b, v17.8b, v18.8b }, [x0], #24
        sub	x2, x2, #0x1
        cbnz	x2, poly_tobytes_asm_asm_loop_start
        ret

#endif /* MLK_ARITH_BACKEND_AARCH64 &&
          !MLK_MULTILEVEL_BUILD_NO_SHARED */
