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

#include "../abicheck_x86_64.h"
#include "../checks_x86_64_all.h"

#if defined(MLK_SYS_X86_64) && defined(MLK_SYSV_ABI_SUPPORTED) && \
    defined(__AVX2__)

#include "../../../notrandombytes/notrandombytes.h"

typedef struct x86_64_register_state reg_state;

MLK_SYSV_ABI
void mlk_nttunpack_avx2_asm(int16_t *r);

int check_nttunpack_avx2_asm(void)
{
  int test_iter;
  reg_state input_state, output_state;
  int violations;
  MLK_ALIGN uint8_t buf_rdi[512]; /* Input/output polynomial (256 x int16_t) */

  if (!mlk_sys_check_capability(MLK_SYS_CAP_X86_64_AVX2))
  {
    fprintf(stderr,
            "ABI check nttunpack_avx2_asm: host lacks AVX2, skipping\n");
    return MLK_ABICHECK_SKIPPED;
  }

  for (test_iter = 0; test_iter < MLK_ABICHECK_NUM_TESTS; test_iter++)
  {
    /* Initialize random register state */
    init_x86_64_register_state(&input_state);

    randombytes(buf_rdi, 512);

    /* Set up register state for function arguments */
    input_state.rdi = (uint64_t)buf_rdi;

    /* Call function through ABI test stub */
    asm_call_stub_x86_64_sysv(
        &input_state, &output_state,
        (MLK_SYSV_ABI
         void (*)(void))mlk_nttunpack_avx2_asm);

    /* Check ABI compliance */
    violations = check_x86_64_sysv_compliance(&input_state, &output_state,
                                              MLK_ABICHECK_VERBOSE);
    if (violations > 0)
    {
      fprintf(stderr,
              "ABI test FAILED for nttunpack_avx2_asm (iteration %d): %d "
              "violations\n",
              test_iter + 1, violations);
      return MLK_ABICHECK_FAILED;
    }
  }

  return MLK_ABICHECK_PASSED;
}

#endif /* MLK_SYS_X86_64 && MLK_SYSV_ABI_SUPPORTED && __AVX2__ */
