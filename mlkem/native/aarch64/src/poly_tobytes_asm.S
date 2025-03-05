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
        ld2	{ v11.8h, v12.8h }, [x1], #32
        xtn	v2.8b, v12.8h
        shrn	v14.8b, v12.8h, #0x4
        xtn	v12.8b, v11.8h
        shrn	v13.8b, v11.8h, #0x8
        sli	v13.8b, v2.8b, #0x4
        sub	x2, x2, #0x1

poly_tobytes_asm_asm_loop_start:
        ld2	{ v24.8h, v25.8h }, [x1], #32
        st3	{ v12.8b, v13.8b, v14.8b }, [x0], #24
        xtn	v12.8b, v25.8h
        shrn	v13.8b, v24.8h, #0x8
        sli	v13.8b, v12.8b, #0x4
        shrn	v14.8b, v25.8h, #0x4
        xtn	v12.8b, v24.8h
        sub	x2, x2, #0x1
        cbnz	x2, poly_tobytes_asm_asm_loop_start
        st3	{ v12.8b, v13.8b, v14.8b }, [x0], #24
        ret

#endif /* MLK_ARITH_BACKEND_AARCH64_OPT &&
          !MLK_MULTILEVEL_BUILD_NO_SHARED */
