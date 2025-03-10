/*
 * Copyright (c) 2024-2025 The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0
 */

#include "../../../common.h"
#if defined(MLK_ARITH_BACKEND_AARCH64_OPT) && \
    !defined(MLK_MULTILEVEL_BUILD_NO_SHARED)

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
        ld2	{ v8.8h, v9.8h }, [x1], #32
        ld2	{ v17.8h, v18.8h }, [x1], #32
        xtn	v25.8b, v8.8h
        xtn	v28.8b, v9.8h
        xtn	v19.8b, v17.8h
        shrn	v20.8b, v17.8h, #0x8
        xtn	v5.8b, v18.8h
        shrn	v21.8b, v18.8h, #0x4
        shrn	v26.8b, v8.8h, #0x8
        sli	v26.8b, v28.8b, #0x4
        shrn	v27.8b, v9.8h, #0x4
        st3	{ v25.8b, v26.8b, v27.8b }, [x0], #24
        sli	v20.8b, v5.8b, #0x4
        ld2	{ v1.8h, v2.8h }, [x1], #32
        st3	{ v19.8b, v20.8b, v21.8b }, [x0], #24
        xtn	v29.8b, v2.8h
        shrn	v7.8b, v2.8h, #0x4
        shrn	v6.8b, v1.8h, #0x8
        xtn	v5.8b, v1.8h
        ld2	{ v1.8h, v2.8h }, [x1], #32
        sli	v6.8b, v29.8b, #0x4
        xtn	v8.8b, v1.8h
        xtn	v25.8b, v2.8h
        shrn	v10.8b, v2.8h, #0x4
        st3	{ v5.8b, v6.8b, v7.8b }, [x0], #24
        shrn	v9.8b, v1.8h, #0x8
        sli	v9.8b, v25.8b, #0x4
        st3	{ v8.8b, v9.8b, v10.8b }, [x0], #24
        sub	x2, x2, #0x1
        cbnz	x2, poly_tobytes_asm_asm_loop_start
        ret

#endif /* MLK_ARITH_BACKEND_AARCH64_OPT &&
          !MLK_MULTILEVEL_BUILD_NO_SHARED */
