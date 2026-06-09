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

#include <stdio.h>

#include "abicheckutil.h"
#include "checks_all.h"

#if defined(MLK_SYS_PPC64LE)

#include "../notrandombytes/notrandombytes.h"

typedef struct ppc64le_register_state reg_state;

#define NUM_TESTS 3

void mlk_poly_tomont_ppc_asm(int16_t *r, const int16_t *qdata);

int check_poly_tomont_ppc_asm_powerpc64le(void)
{
  int test_iter;
  reg_state input_state, output_state;
  int violations;
  MLK_ALIGN uint8_t buf_r3[512];  /* Input/output polynomial (256 x int16_t) */
  MLK_ALIGN uint8_t buf_r4[4144]; /* Precomputed constants (2072 x int16_t) */

  for (test_iter = 0; test_iter < NUM_TESTS; test_iter++)
  {
    /* Initialize random register state */
    init_ppc64le_register_state(&input_state);

    /* Initialize buffer for r3 */
    randombytes(buf_r3, 512);
    /* Initialize buffer for r4 */
    randombytes(buf_r4, 4144);

    /* Set up register state for function arguments */
    input_state.gpr_arg[0] = (uint64_t)buf_r3;
    input_state.gpr_arg[1] = (uint64_t)buf_r4;

    /* Call function through ABI test stub */
    asm_call_stub_ppc64le(&input_state, &output_state,
                          (void (*)(void))mlk_poly_tomont_ppc_asm);

    /* Check ABI compliance */
    violations = check_ppc64le_elfv2_compliance(&input_state, &output_state);
    if (violations > 0)
    {
      fprintf(stderr,
              "ABI test FAILED for poly_tomont_ppc_asm (iteration %d): %d "
              "violations\n",
              test_iter + 1, violations);
      return 1;
    }
  }

  return 0;
}

#else /* MLK_SYS_PPC64LE */

int check_poly_tomont_ppc_asm_powerpc64le(void)
{
  fprintf(
      stderr,
      "ABI check poly_tomont_ppc_asm_powerpc64le: unsupported architecture\n");
  return 1;
}

#endif /* !MLK_SYS_PPC64LE */
