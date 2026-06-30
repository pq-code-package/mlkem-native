/*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */

/*
 * WARNING: This file is auto-generated from scripts/autogen
 *          in the mlkem-native repository.
 *          Do not modify it directly.
 */

#include <stdio.h>

#include "../abicheck_armv81m.h"
#include "../checks_armv81m_all.h"

#if defined(MLK_SYS_ARMV81M_MVE) && defined(__ARM_FEATURE_MVE)

#include "../../../notrandombytes/notrandombytes.h"

typedef struct armv81m_register_state reg_state;

void mlk_keccak_f1600_x4_mve_asm(void *state, void *tmpstate,
                                 const uint32_t *rc);

int check_keccak_f1600_x4_mve_asm(void)
{
  int test_iter;
  reg_state input_state, output_state;
  int violations;
  MLK_ALIGN uint8_t buf_r0[800]; /* Bit-interleaved state for 4 Keccak instances
                                    (even halves followed by odd halves) */
  MLK_ALIGN uint8_t buf_r1[800]; /* Temporary storage for intermediate state */
  MLK_ALIGN uint8_t buf_r2[192]; /* Keccak round constants in bit-interleaved
                                    form (24 pairs of 32-bit words) */

  if (!mlk_sys_check_capability(MLK_SYS_CAP_ARMV81M_MVE))
  {
    fprintf(stderr,
            "ABI check keccak_f1600_x4_mve_asm: host lacks Armv8.1-M MVE, "
            "skipping\n");
    return MLK_ABICHECK_SKIPPED;
  }

  for (test_iter = 0; test_iter < MLK_ABICHECK_NUM_TESTS; test_iter++)
  {
    /* Initialize random register state */
    init_armv81m_register_state(&input_state);

    randombytes(buf_r0, 800);
    randombytes(buf_r1, 800);
    randombytes(buf_r2, 192);

    /* Set up register state for function arguments */
    input_state.gpr[0] = (uint32_t)buf_r0;
    input_state.gpr[1] = (uint32_t)buf_r1;
    input_state.gpr[2] = (uint32_t)buf_r2;

    /* Call function through ABI test stub */
    asm_call_stub_armv81m(&input_state, &output_state,
                          (void (*)(void))mlk_keccak_f1600_x4_mve_asm);

    /* Check ABI compliance */
    violations = check_armv81m_aapcs32_compliance(&input_state, &output_state,
                                                  MLK_ABICHECK_VERBOSE);
    if (violations > 0)
    {
      fprintf(stderr,
              "ABI test FAILED for keccak_f1600_x4_mve_asm (iteration %d): %d "
              "violations\n",
              test_iter + 1, violations);
      return MLK_ABICHECK_FAILED;
    }
  }

  return MLK_ABICHECK_PASSED;
}

#endif /* MLK_SYS_ARMV81M_MVE && __ARM_FEATURE_MVE */
