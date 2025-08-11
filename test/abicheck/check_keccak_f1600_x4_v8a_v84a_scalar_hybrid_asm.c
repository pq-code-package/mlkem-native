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

#if defined(__ARM_FEATURE_SHA3)

#include <stdio.h>
#include <string.h>

#include "../notrandombytes/notrandombytes.h"
#include "abicheckutil.h"
#include "checks_all.h"

typedef struct register_state register_state;

#define NUM_TESTS 3

void mlk_keccak_f1600_x4_v8a_v84a_scalar_hybrid_asm(uint64_t state[100],
                                                    const uint64_t rc[24]);

int check_keccak_f1600_x4_v8a_v84a_scalar_hybrid_asm(void)
{
  int test_iter;
  register_state input_state, output_state;
  int violations;
  MLK_ALIGN uint8_t buf_x0[800]; /* Four sequential Keccak states (state0[25],
                                    state1[25], state2[25], state3[25]) */
  MLK_ALIGN uint8_t buf_x1[192]; /* Round constants (24 x uint64_t) */

  for (test_iter = 0; test_iter < NUM_TESTS; test_iter++)
  {
    /* Initialize random register state */
    init_random_register_state(&input_state);

    /* Initialize buffer for x0 */
    randombytes(buf_x0, 800);
    /* Initialize buffer for x1 */
    randombytes(buf_x1, 192);

    /* Set up register state for function arguments */
    input_state.gpr[0] = (uint64_t)buf_x0;
    input_state.gpr[1] = (uint64_t)buf_x1;

    /* Call function through ABI test stub */
    asm_call_stub(
        &input_state, &output_state,
        (void (*)(void))mlk_keccak_f1600_x4_v8a_v84a_scalar_hybrid_asm);

    /* Check ABI compliance */
    violations = check_aarch64_aapcs_compliance(&input_state, &output_state);
    if (violations > 0)
    {
      fprintf(stderr,
              "ABI test FAILED for keccak_f1600_x4_v8a_v84a_scalar_hybrid_asm "
              "(iteration %d): %d violations\n",
              test_iter + 1, violations);
      return 1;
    }
  }

  return 0;
}

#else /* __ARM_FEATURE_SHA3 */

#include "../../mlkem/src/common.h"
MLK_EMPTY_CU(check_keccak_f1600_x4_v8a_v84a_scalar_hybrid_asm)

#endif /* !__ARM_FEATURE_SHA3 */

#else /* MLK_SYS_AARCH64 */

#include "../../mlkem/src/common.h"
MLK_EMPTY_CU(check_keccak_f1600_x4_v8a_v84a_scalar_hybrid_asm)

#endif /* !MLK_SYS_AARCH64 */
