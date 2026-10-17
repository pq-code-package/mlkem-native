/*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */

/* NOTE: You can remove this file unless you compile with MLKEM_DEBUG. */

#include "../../../common.h"

#if defined(MLK_ARITH_BACKEND_RISCV64) &&                                \
    !defined(MLK_CONFIG_MULTILEVEL_NO_SHARED) && defined(MLKEM_DEBUG) && \
    !defined(CBMC)

#include "rv64v_debug.h"

/**
 * Check whether values in a vint16m1_t vector are within specified bounds.
 *
 * @param[in] file                  Filename.
 * @param     file_len              Length of @p file, including its
 *                                  terminating null byte.
 * @param     line                  Line number.
 * @param     vec                   RISC-V vector to be checked.
 * @param     vl                    Vector length (number of active elements).
 * @param     lower_bound_exclusive Exclusive lower bound.
 * @param     upper_bound_exclusive Exclusive upper bound.
 */
void mlk_debug_check_bounds_int16m1(const char *file, size_t file_len, int line,
                                    vint16m1_t vec, size_t vl,
                                    int lower_bound_exclusive,
                                    int upper_bound_exclusive)
{
  /* Allocate temporary array to store vector elements.
   * vl is at most MLKEM_N, as it is always obtained from
   * vsetvl with an AVL of at most MLKEM_N. */
  int16_t temp_array[MLKEM_N];

  mlk_debug_check_assert(file, file_len, line, vl <= MLKEM_N);
  __riscv_vse16_v_i16m1(temp_array, vec, vl);

  mlk_debug_check_bounds(file, file_len, line, temp_array, (unsigned)vl,
                         lower_bound_exclusive, upper_bound_exclusive);
}

#else /* MLK_ARITH_BACKEND_RISCV64 && !MLK_CONFIG_MULTILEVEL_NO_SHARED && \
         MLKEM_DEBUG && !CBMC */

MLK_EMPTY_CU(rv64v_debug)

#endif /* !(MLK_ARITH_BACKEND_RISCV64 && !MLK_CONFIG_MULTILEVEL_NO_SHARED && \
          MLKEM_DEBUG && !CBMC) */
