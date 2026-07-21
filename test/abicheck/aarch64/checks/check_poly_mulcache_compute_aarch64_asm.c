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

#include "../abicheck_aarch64.h"
#include "../checks_aarch64_all.h"

#if defined(MLK_SYS_AARCH64) && defined(MLK_SYS_AARCH64_NEON)

#include "../../../notrandombytes/notrandombytes.h"

typedef struct aarch64_register_state reg_state;

void mlk_poly_mulcache_compute_aarch64_asm(int16_t cache[128],
                                           const int16_t mlk_poly[256],
                                           const int16_t zetas[128],
                                           const int16_t zetas_twisted[128]);

int check_poly_mulcache_compute_aarch64_asm(void)
{
  int test_iter;
  reg_state input_state, output_state;
  int violations;
  MLK_ALIGN uint8_t buf_x0[256]; /* Output cache */
  MLK_ALIGN uint8_t buf_x1[512]; /* Input polynomial */
  MLK_ALIGN uint8_t buf_x2[256]; /* Zeta values */
  MLK_ALIGN uint8_t buf_x3[256]; /* Twisted zeta values */

  if (!mlk_sys_check_capability(MLK_SYS_CAP_NEON))
  {
    fprintf(stderr,
            "ABI check poly_mulcache_compute_aarch64_asm: host lacks AArch64 "
            "NEON, skipping\n");
    return MLK_ABICHECK_SKIPPED;
  }

  for (test_iter = 0; test_iter < MLK_ABICHECK_NUM_TESTS; test_iter++)
  {
    /* Initialize random register state */
    init_aarch64_register_state(&input_state);

    randombytes(buf_x0, 256);
    randombytes(buf_x1, 512);
    randombytes(buf_x2, 256);
    randombytes(buf_x3, 256);

    /* Set up register state for function arguments */
    input_state.gpr[0] = (uint64_t)buf_x0;
    input_state.gpr[1] = (uint64_t)buf_x1;
    input_state.gpr[2] = (uint64_t)buf_x2;
    input_state.gpr[3] = (uint64_t)buf_x3;

    /* Call function through ABI test stub */
    call_stub_aarch64(&input_state, &output_state,
                      (void (*)(void))mlk_poly_mulcache_compute_aarch64_asm);

    /* Check ABI compliance */
    violations = check_aarch64_aapcs_compliance(&input_state, &output_state,
                                                MLK_ABICHECK_VERBOSE);
    if (violations > 0)
    {
      fprintf(stderr,
              "ABI test FAILED for poly_mulcache_compute_aarch64_asm "
              "(iteration %d): %d violations\n",
              test_iter + 1, violations);
      return MLK_ABICHECK_FAILED;
    }
  }

  return MLK_ABICHECK_PASSED;
}

#endif /* MLK_SYS_AARCH64 && MLK_SYS_AARCH64_NEON */
