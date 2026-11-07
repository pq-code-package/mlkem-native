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

#include "../abicheck_riscv64.h"
#include "../checks_riscv64_all.h"

#if defined(MLK_SYS_RISCV64) && defined(MLK_SYS_RISCV64_RVV)

#include "../../../notrandombytes/notrandombytes.h"

typedef struct riscv64_register_state reg_state;

void mlk_polyvec_basemul_acc_montgomery_cached_k2_riscv64_asm(
    int16_t r[256], const int16_t a[512], const int16_t b[512],
    const int16_t b_cache[256]);

int check_polyvec_basemul_acc_montgomery_cached_k2_riscv64_asm(void)
{
  int test_iter;
  reg_state input_state, output_state;
  int violations;
  MLK_ALIGN uint8_t buf_a0[512]; /* Output polynomial */
  MLK_ALIGN uint8_t
      buf_a1[1024]; /* Input polynomial vector a (2 x 256 x int16_t) */
  MLK_ALIGN uint8_t
      buf_a2[1024]; /* Input polynomial vector b (2 x 256 x int16_t) */
  MLK_ALIGN uint8_t
      buf_a3[512]; /* Multiplication cache of b (2 x 128 x int16_t) */

  for (test_iter = 0; test_iter < MLK_ABICHECK_NUM_TESTS; test_iter++)
  {
    /* Initialize random register state */
    init_riscv64_register_state(&input_state);

    randombytes(buf_a0, 512);
    randombytes(buf_a1, 1024);
    randombytes(buf_a2, 1024);
    randombytes(buf_a3, 512);

    /* Set up register state for function arguments */
    input_state.gpr[10] = (uint64_t)buf_a0;
    input_state.gpr[11] = (uint64_t)buf_a1;
    input_state.gpr[12] = (uint64_t)buf_a2;
    input_state.gpr[13] = (uint64_t)buf_a3;

    /* Call function through ABI test stub */
    asm_call_stub_riscv64(
        &input_state, &output_state,
        (void (*)(
            void))mlk_polyvec_basemul_acc_montgomery_cached_k2_riscv64_asm);

    /* Check ABI compliance */
    violations = check_riscv64_lp64d_compliance(&input_state, &output_state,
                                                MLK_ABICHECK_VERBOSE);
    if (violations > 0)
    {
      fprintf(stderr,
              "ABI test FAILED for "
              "polyvec_basemul_acc_montgomery_cached_k2_riscv64_asm (iteration "
              "%d): %d violations\n",
              test_iter + 1, violations);
      return MLK_ABICHECK_FAILED;
    }
  }

  return MLK_ABICHECK_PASSED;
}

#endif /* MLK_SYS_RISCV64 && MLK_SYS_RISCV64_RVV */
