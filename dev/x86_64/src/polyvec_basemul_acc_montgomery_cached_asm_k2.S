/*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */

#include "../../../common.h"
#if defined(MLK_ARITH_BACKEND_X86_64_DEFAULT) && \
    !defined(MLK_CONFIG_MULTILEVEL_NO_SHARED) && \
    (defined(MLK_CONFIG_MULTILEVEL_WITH_SHARED) || MLKEM_K == 2)
/* simpasm: header-end */

#include "consts.h"
#include "poly_basemul.inc"

.global MLK_ASM_NAMESPACE(polyvec_basemul_acc_montgomery_cached_asm_k2)
.balign 4
MLK_ASM_FN_SYMBOL(polyvec_basemul_acc_montgomery_cached_asm_k2)
.cfi_startproc
polyvec_basemul 2
ret
.cfi_endproc

/* simpasm: footer-start */
#endif /* MLK_ARITH_BACKEND_X86_64_DEFAULT && !MLK_CONFIG_MULTILEVEL_NO_SHARED \
          && (MLK_CONFIG_MULTILEVEL_WITH_SHARED || MLKEM_K == 2) */
