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

void mlk_ntt_vlen256_riscv64_asm(int16_t p[256], const int16_t zetas[800],
                                 const uint16_t perms[160]);

int check_ntt_vlen256_riscv64_asm(void)
{
  int test_iter;
  reg_state input_state, output_state;
  int violations;
  MLK_ALIGN uint8_t buf_a0[512];  /* Input/output polynomial */
  MLK_ALIGN uint8_t buf_a1[1600]; /* Twiddle table (mlk_rv64v_ntt256_zetas) */
  MLK_ALIGN uint8_t
      buf_a2[320]; /* Permutation table (mlk_rv64v_ntt256_perms) */

  for (test_iter = 0; test_iter < MLK_ABICHECK_NUM_TESTS; test_iter++)
  {
    /* Initialize random register state */
    init_riscv64_register_state(&input_state);

    randombytes(buf_a0, 512);
    randombytes(buf_a1, 1600);
    randombytes(buf_a2, 320);

    /* Set up register state for function arguments */
    input_state.gpr[10] = (uint64_t)buf_a0;
    input_state.gpr[11] = (uint64_t)buf_a1;
    input_state.gpr[12] = (uint64_t)buf_a2;

    /* Call function through ABI test stub */
    asm_call_stub_riscv64(&input_state, &output_state,
                          (void (*)(void))mlk_ntt_vlen256_riscv64_asm);

    /* Check ABI compliance */
    violations = check_riscv64_lp64d_compliance(&input_state, &output_state,
                                                MLK_ABICHECK_VERBOSE);
    if (violations > 0)
    {
      fprintf(stderr,
              "ABI test FAILED for ntt_vlen256_riscv64_asm (iteration %d): %d "
              "violations\n",
              test_iter + 1, violations);
      return MLK_ABICHECK_FAILED;
    }
  }

  return MLK_ABICHECK_PASSED;
}

#endif /* MLK_SYS_RISCV64 && MLK_SYS_RISCV64_RVV */
