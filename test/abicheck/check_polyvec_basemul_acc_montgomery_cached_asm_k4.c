/*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */

/*
 * WARNING: This file is auto-generated from scripts/autogen
 *          in the mlkem-native repository.
 *          Do not modify it directly.
 */


#include "../../mlkem/src/sys.h"

#if defined(MLK_SYS_AARCH64)

#include <stdio.h>
#include <string.h>

#include "../notrandombytes/notrandombytes.h"
#include "abicheckutil.h"
#include "checks_all.h"

typedef struct register_state register_state;

#define NUM_TESTS 3

void mlk_polyvec_basemul_acc_montgomery_cached_asm_k4(
    int16_t r[256], const int16_t a[1024], const int16_t b[1024],
    const int16_t b_cache[512]);

int check_polyvec_basemul_acc_montgomery_cached_asm_k4(void)
{
  int test_iter;
  register_state input_state, output_state;
  int violations;
  MLK_ALIGN uint8_t buf_x0[512];  /* Output polynomial */
  MLK_ALIGN uint8_t buf_x1[2048]; /* Input polynomial vector a */
  MLK_ALIGN uint8_t buf_x2[2048]; /* Input polynomial vector b */
  MLK_ALIGN uint8_t buf_x3[1024]; /* Cached values for b */

  for (test_iter = 0; test_iter < NUM_TESTS; test_iter++)
  {
    /* Initialize random register state */
    init_random_register_state(&input_state);

    /* Initialize buffer for x0 */
    randombytes(buf_x0, 512);
    /* Initialize buffer for x1 */
    randombytes(buf_x1, 2048);
    /* Initialize buffer for x2 */
    randombytes(buf_x2, 2048);
    /* Initialize buffer for x3 */
    randombytes(buf_x3, 1024);

    /* Set up register state for function arguments */
    input_state.gpr[0] = (uint64_t)buf_x0;
    input_state.gpr[1] = (uint64_t)buf_x1;
    input_state.gpr[2] = (uint64_t)buf_x2;
    input_state.gpr[3] = (uint64_t)buf_x3;

    /* Call function through ABI test stub */
    asm_call_stub(
        &input_state, &output_state,
        (void (*)(void))mlk_polyvec_basemul_acc_montgomery_cached_asm_k4);

    /* Check ABI compliance */
    violations = check_aarch64_aapcs_compliance(&input_state, &output_state);
    if (violations > 0)
    {
      fprintf(
          stderr,
          "ABI test FAILED for polyvec_basemul_acc_montgomery_cached_asm_k4 "
          "(iteration %d): %d violations\n",
          test_iter + 1, violations);
      return 1;
    }
  }

  return 0;
}

#else /* MLK_SYS_AARCH64 */

#include "../../mlkem/src/common.h"
MLK_EMPTY_CU(check_polyvec_basemul_acc_montgomery_cached_asm_k4)

#endif /* !MLK_SYS_AARCH64 */
