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

uint64_t mlk_rej_uniform_asm(int16_t r[256], const uint8_t *buf,
                             unsigned buflen, const uint8_t table[2048]);

int check_rej_uniform_asm(void)
{
  int test_iter;
  register_state input_state, output_state;
  int violations;
  MLK_ALIGN uint8_t buf_x0[512];  /* Output buffer */
  MLK_ALIGN uint8_t buf_x1[504];  /* Input buffer */
  MLK_ALIGN uint8_t buf_x3[2048]; /* Lookup table */

  for (test_iter = 0; test_iter < NUM_TESTS; test_iter++)
  {
    /* Initialize random register state */
    init_random_register_state(&input_state);

    /* Initialize buffer for x0 */
    randombytes(buf_x0, 512);
    /* Initialize buffer for x1 */
    randombytes(buf_x1, 504);
    /* Initialize buffer for x3 */
    randombytes(buf_x3, 2048);

    /* Set up register state for function arguments */
    input_state.gpr[0] = (uint64_t)buf_x0;
    input_state.gpr[1] = (uint64_t)buf_x1;
    input_state.gpr[2] = 504;
    input_state.gpr[3] = (uint64_t)buf_x3;

    /* Call function through ABI test stub */
    asm_call_stub(&input_state, &output_state,
                  (void (*)(void))mlk_rej_uniform_asm);

    /* Check ABI compliance */
    violations = check_aarch64_aapcs_compliance(&input_state, &output_state);
    if (violations > 0)
    {
      fprintf(
          stderr,
          "ABI test FAILED for rej_uniform_asm (iteration %d): %d violations\n",
          test_iter + 1, violations);
      return 1;
    }
  }

  return 0;
}

#else /* MLK_SYS_AARCH64 */

#include "../../mlkem/src/common.h"
MLK_EMPTY_CU(check_rej_uniform_asm)

#endif /* !MLK_SYS_AARCH64 */
