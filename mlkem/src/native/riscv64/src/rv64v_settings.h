/*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */
#ifndef MLK_NATIVE_RISCV64_SRC_RV64V_SETTINGS_H
#define MLK_NATIVE_RISCV64_SRC_RV64V_SETTINGS_H

#include <riscv_vector.h>
#include "../../../debug.h"

/*************************************************
 * RISC-V Vector Bounds Assertion Macros
 *
 * These macros provide runtime bounds checking for RISC-V vector types
 * vint16m1_t and vint16m2_t, following the same pattern as the scalar
 * bounds assertions in debug.h
 *
 * The macros are only active when MLKEM_DEBUG is defined, otherwise they
 * compile to no-ops for zero runtime overhead in release builds.
 **************************************************/

#if defined(MLKEM_DEBUG)

/*************************************************
 * Name:        mlk_debug_check_bounds_int16m1
 *
 * Description: Check whether values in a vint16m1_t vector
 *              are within specified bounds.
 *
 * Arguments:   - file: filename
 *              - line: line number
 *              - vec: RISC-V vector to be checked
 *              - vl: vector length (number of active elements)
 *              - lower_bound_exclusive: Exclusive lower bound
 *              - upper_bound_exclusive: Exclusive upper bound
 **************************************************/
#define mlk_debug_check_bounds_int16m1 \
  MLK_NAMESPACE(mlkem_debug_check_bounds_int16m1)
void mlk_debug_check_bounds_int16m1(const char *file, int line, vint16m1_t vec,
                                    size_t vl, int lower_bound_exclusive,
                                    int upper_bound_exclusive);

/*************************************************
 * Name:        mlk_debug_check_bounds_int16m2
 *
 * Description: Check whether values in a vint16m2_t vector
 *              are within specified bounds by splitting into m1 vectors.
 *
 * Arguments:   - file: filename
 *              - line: line number
 *              - vec: RISC-V vector to be checked
 *              - vl: vector length (number of active elements per m1 half)
 *              - lower_bound_exclusive: Exclusive lower bound
 *              - upper_bound_exclusive: Exclusive upper bound
 **************************************************/
#define mlk_debug_check_bounds_int16m2 \
  MLK_NAMESPACE(mlkem_debug_check_bounds_int16m2)
void mlk_debug_check_bounds_int16m2(const char *file, int line, vint16m2_t vec,
                                    size_t vl, int lower_bound_exclusive,
                                    int upper_bound_exclusive);

/* Check bounds in vint16m1_t vector
 * vec: RISC-V vector of type vint16m1_t
 * vl: Vector length (number of active elements)
 * value_lb: Inclusive lower value bound
 * value_ub: Exclusive upper value bound */
#define mlk_assert_bound_int16m1(vec, vl, value_lb, value_ub)     \
  mlk_debug_check_bounds_int16m1(__FILE__, __LINE__, (vec), (vl), \
                                 (value_lb) - 1, (value_ub))

/* Check absolute bounds in vint16m1_t vector
 * vec: RISC-V vector of type vint16m1_t
 * vl: Vector length (number of active elements)
 * value_abs_bd: Exclusive absolute upper bound */
#define mlk_assert_abs_bound_int16m1(vec, vl, value_abs_bd) \
  mlk_assert_bound_int16m1((vec), (vl), (-(value_abs_bd) + 1), (value_abs_bd))

/* Check bounds in vint16m2_t vector
 * vec: RISC-V vector of type vint16m2_t
 * vl: Vector length (number of active elements per m1 half)
 * value_lb: Inclusive lower value bound
 * value_ub: Exclusive upper value bound */
#define mlk_assert_bound_int16m2(vec, vl, value_lb, value_ub)     \
  mlk_debug_check_bounds_int16m2(__FILE__, __LINE__, (vec), (vl), \
                                 (value_lb) - 1, (value_ub))

/* Check absolute bounds in vint16m2_t vector
 * vec: RISC-V vector of type vint16m2_t
 * vl: Vector length (number of active elements per m1 half)
 * value_abs_bd: Exclusive absolute upper bound */
#define mlk_assert_abs_bound_int16m2(vec, vl, value_abs_bd) \
  mlk_assert_bound_int16m2((vec), (vl), (-(value_abs_bd) + 1), (value_abs_bd))

#elif defined(CBMC)

/* For CBMC, we would need to implement vector bounds checking using CBMC
 * primitives This is complex and would require extracting vector elements, so
 * for now we provide empty implementations that could be extended later */
#define mlk_assert_bound_int16m1(vec, vl, value_lb, value_ub) \
  do                                                          \
  {                                                           \
  } while (0)

#define mlk_assert_abs_bound_int16m1(vec, vl, value_abs_bd) \
  do                                                        \
  {                                                         \
  } while (0)

#define mlk_assert_bound_int16m2(vec, vl, value_lb, value_ub) \
  do                                                          \
  {                                                           \
  } while (0)

#define mlk_assert_abs_bound_int16m2(vec, vl, value_abs_bd) \
  do                                                        \
  {                                                         \
  } while (0)

#else /* !MLKEM_DEBUG && CBMC */

/* When debugging is disabled, all assertions become no-ops */
#define mlk_assert_bound_int16m1(vec, vl, value_lb, value_ub) \
  do                                                          \
  {                                                           \
  } while (0)

#define mlk_assert_abs_bound_int16m1(vec, vl, value_abs_bd) \
  do                                                        \
  {                                                         \
  } while (0)

#define mlk_assert_bound_int16m2(vec, vl, value_lb, value_ub) \
  do                                                          \
  {                                                           \
  } while (0)

#define mlk_assert_abs_bound_int16m2(vec, vl, value_abs_bd) \
  do                                                        \
  {                                                         \
  } while (0)

#endif /* !MLKEM_DEBUG && !CBMC */

/*  === vector configuration */
#ifndef MLK_RVV_VLEN
#define MLK_RVV_VLEN 256
#endif



/*  vl value for a 16-bit wide type */
#define MLK_RVV_E16M1_VL (MLK_RVV_VLEN / 16)

/*  Montgomery reduction constants */
/*  n   = 256; q   = 3329; r   = 2^16 */
/* check-magic: 3327 == unsigned_mod(-pow(MLKEM_Q,-1,2^16), 2^16) */
#define MLK_RVV_QI 3327

/* check-magic: 2285 == unsigned_mod(2^16, MLKEM_Q) */
#define MLK_RVV_MONT_R1 2285

/* check-magic: 1353 == pow(2, 32, MLKEM_Q) */
#define MLK_RVV_MONT_R2 1353

/* check-magic: 1441 == pow(2,32-7,MLKEM_Q) */
#define MLK_RVV_MONT_NR 1441

#endif /* !MLK_NATIVE_RISCV64_SRC_RV64V_SETTINGS_H */
