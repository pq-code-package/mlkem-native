/*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */

/*
 * WARNING: This file is auto-generated from scripts/autogen
 *          in the mlkem-native repository.
 *          Do not modify it directly.
 */

#include "../abicheck_prologue.h"

#include <stdio.h>

#include "../abicheckutil.h"
#include "checks_aarch64_all.h"

#if defined(MLK_SYS_AARCH64)

#include "../../notrandombytes/notrandombytes.h"

typedef struct aarch64_register_state reg_state;

void mlk_poly_tobytes_aarch64_asm(uint8_t r[384], const int16_t a[256]);

int check_poly_tobytes_aarch64_asm(void)
{
  int test_iter;
  reg_state input_state, output_state;
  int violations;
  MLK_ALIGN uint8_t buf_x0[384]; /* Output byte array */
  MLK_ALIGN uint8_t buf_x1[512]; /* Input polynomial */

  for (test_iter = 0; test_iter < MLK_ABICHECK_NUM_TESTS; test_iter++)
  {
    /* Initialize random register state */
    init_aarch64_register_state(&input_state);

    randombytes(buf_x0, 384);
    randombytes(buf_x1, 512);

    /* Set up register state for function arguments */
    input_state.gpr[0] = (uint64_t)buf_x0;
    input_state.gpr[1] = (uint64_t)buf_x1;

    /* Call function through ABI test stub */
    asm_call_stub_aarch64(&input_state, &output_state,
                          (void (*)(void))mlk_poly_tobytes_aarch64_asm);

    /* Check ABI compliance */
    violations = check_aarch64_aapcs_compliance(&input_state, &output_state,
                                                MLK_ABICHECK_VERBOSE);
    if (violations > 0)
    {
      fprintf(stderr,
              "ABI test FAILED for poly_tobytes_aarch64_asm (iteration %d): %d "
              "violations\n",
              test_iter + 1, violations);
      return MLK_ABICHECK_FAILED;
    }
  }

  return MLK_ABICHECK_PASSED;
}

#endif /* defined(MLK_SYS_AARCH64) */
