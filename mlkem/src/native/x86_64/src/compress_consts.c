/*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */

/*
 * WARNING: This file is auto-generated from scripts/autogen
 *          in the mlkem-native repository.
 *          Do not modify it directly.
 */

#include "../../../common.h"

#if defined(MLK_ARITH_BACKEND_X86_64_DEFAULT)

#include "compress_consts.h"

#if !defined(MLK_CONFIG_MULTILEVEL_NO_SHARED) &&                   \
    (defined(MLK_CONFIG_MULTILEVEL_WITH_SHARED) || MLKEM_K == 2 || \
     MLKEM_K == 3)

MLK_ALIGN const uint8_t mlk_decompress_d4_data[32] = {
    0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 3,
    4, 4, 4, 4, 5, 5, 5, 5, 6, 6, 6, 6, 7, 7, 7, 7, /* shufbidx */
};

#endif /* !MLK_CONFIG_MULTILEVEL_NO_SHARED &&                                 \
          (MLK_CONFIG_MULTILEVEL_WITH_SHARED || MLKEM_K == 2 || MLKEM_K == 3) \
        */

#else /* MLK_ARITH_BACKEND_X86_64_DEFAULT */

MLK_EMPTY_CU(avx2_compress_consts)

#endif /* !MLK_ARITH_BACKEND_X86_64_DEFAULT */
