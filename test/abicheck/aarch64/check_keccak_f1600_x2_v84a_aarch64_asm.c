/*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */

/*
 * WARNING: This file is auto-generated from scripts/autogen
 *          in the mlkem-native repository.
 *          Do not modify it directly.
 */

#define MLK_BUILD_INTERNAL
#if defined(MLK_CONFIG_FILE)
#include MLK_CONFIG_FILE
#else
#include "../../../mlkem/mlkem_native_config.h"
#endif
#include "../../../mlkem/src/sys.h"

#include <stdio.h>

#include "../abicheckutil.h"
#include "checks_aarch64_all.h"

#if defined(MLK_SYS_AARCH64) && defined(__ARM_FEATURE_SHA3)

#include "../../notrandombytes/notrandombytes.h"

typedef struct register_state reg_state;

void mlk_keccak_f1600_x2_v84a_aarch64_asm(uint64_t state[50],
                                          const uint64_t rc[24]);

int check_keccak_f1600_x2_v84a_aarch64_asm(void)
{
  int test_iter;
  reg_state input_state, output_state;
  int violations;
  MLK_ALIGN uint8_t
      buf_x0[400]; /* Two sequential Keccak states (state0[25], state1[25]) */
  MLK_ALIGN uint8_t buf_x1[192]; /* Round constants (24 x uint64_t) */

  if (!mlk_sys_check_capability(MLK_SYS_CAP_SHA3))
  {
    fprintf(stderr,
            "ABI check keccak_f1600_x2_v84a_aarch64_asm: host lacks Armv8.4-A "
            "SHA3 (eor3, rax1, xar, bcax), skipping\n");
    return MLK_ABICHECK_SKIPPED;
  }

  for (test_iter = 0; test_iter < MLK_ABICHECK_NUM_TESTS; test_iter++)
  {
    /* Initialize random register state */
    init_register_state(&input_state);

    randombytes(buf_x0, 400);
    randombytes(buf_x1, 192);

    /* Set up register state for function arguments */
    input_state.gpr[0] = (uint64_t)buf_x0;
    input_state.gpr[1] = (uint64_t)buf_x1;

    /* Call function through ABI test stub */
    asm_call_stub_aarch64(&input_state, &output_state,
                          (void (*)(void))mlk_keccak_f1600_x2_v84a_aarch64_asm);

    /* Check ABI compliance */
    violations = check_aarch64_aapcs_compliance(&input_state, &output_state,
                                                MLK_ABICHECK_VERBOSE);
    if (violations > 0)
    {
      fprintf(stderr,
              "ABI test FAILED for keccak_f1600_x2_v84a_aarch64_asm (iteration "
              "%d): %d violations\n",
              test_iter + 1, violations);
      return MLK_ABICHECK_FAILED;
    }
  }

  return MLK_ABICHECK_PASSED;
}

#else /* MLK_SYS_AARCH64 && __ARM_FEATURE_SHA3 */

int check_keccak_f1600_x2_v84a_aarch64_asm(void)
{
  fprintf(
      stderr,
      "ABI check keccak_f1600_x2_v84a_aarch64_asm: unsupported architecture\n");
  return MLK_ABICHECK_FAILED;
}

#endif /* !(MLK_SYS_AARCH64 && __ARM_FEATURE_SHA3) */
