/*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */
#ifndef MLK_NATIVE_RISCV64_SRC_RV64V_DEBUG_H
#define MLK_NATIVE_RISCV64_SRC_RV64V_DEBUG_H

#include "../../../debug.h"

/*************************************************
 * RISC-V Vector Bounds Assertion Macros
 *
 * These macros provide runtime bounds checking for RISC-V vint16m1_t values,
 * following the same pattern as the scalar bounds assertions in debug.h.
 *
 * The macros are only active when MLKEM_DEBUG is defined, otherwise they
 * compile to no-ops for zero runtime overhead in release builds.
 **************************************************/

#if defined(MLKEM_DEBUG) && !defined(CBMC)

#include <riscv_vector.h>

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
#define mlk_debug_check_bounds_int16m1 \
  MLK_NAMESPACE(mlkem_debug_check_bounds_int16m1)
void mlk_debug_check_bounds_int16m1(const char *file, size_t file_len, int line,
                                    vint16m1_t vec, size_t vl,
                                    int lower_bound_exclusive,
                                    int upper_bound_exclusive);

/* Check bounds in vint16m1_t vector
 * vec: RISC-V vector of type vint16m1_t
 * vl: Vector length (number of active elements)
 * value_lb: Inclusive lower value bound
 * value_ub: Exclusive upper bound */
#define mlk_assert_bound_int16m1(vec, vl, value_lb, value_ub)                 \
  mlk_debug_check_bounds_int16m1(__FILE__, sizeof(__FILE__), __LINE__, (vec), \
                                 (vl), (value_lb) - 1, (value_ub))

/* Check absolute bounds in vint16m1_t vector
 * vec: RISC-V vector of type vint16m1_t
 * vl: Vector length (number of active elements)
 * value_abs_bd: Exclusive absolute upper bound */
#define mlk_assert_abs_bound_int16m1(vec, vl, value_abs_bd) \
  mlk_assert_bound_int16m1((vec), (vl), (-(value_abs_bd) + 1), (value_abs_bd))

#elif defined(CBMC)

/* CBMC does not model scalable RVV vector types, so callers containing vector
 * operations cannot be compiled by CBMC. */
#define mlk_assert_bound_int16m1(vec, vl, value_lb, value_ub) \
  do                                                          \
  {                                                           \
  } while (0)

#define mlk_assert_abs_bound_int16m1(vec, vl, value_abs_bd) \
  do                                                        \
  {                                                         \
  } while (0)

#else /* !(MLKEM_DEBUG && !CBMC) && CBMC */

/* When debugging is disabled, all assertions become no-ops. */
#define mlk_assert_bound_int16m1(vec, vl, value_lb, value_ub) \
  do                                                          \
  {                                                           \
  } while (0)

#define mlk_assert_abs_bound_int16m1(vec, vl, value_abs_bd) \
  do                                                        \
  {                                                         \
  } while (0)

#endif /* !(MLKEM_DEBUG && !CBMC) && !CBMC */

#endif /* !MLK_NATIVE_RISCV64_SRC_RV64V_DEBUG_H */
