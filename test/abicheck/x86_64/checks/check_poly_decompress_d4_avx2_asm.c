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
void mlk_poly_decompress_d4_avx2_asm(int16_t *r, const uint8_t *a,
                                     const uint8_t *data);

int check_poly_decompress_d4_avx2_asm(void)
{
  int test_iter;
  reg_state input_state, output_state;
  int violations;
  MLK_ALIGN uint8_t buf_rdi[512]; /* Output polynomial (256 x int16_t) */
  MLK_ALIGN uint8_t buf_rdx[32];  /* Precomputed decompression constants */
  MLK_ALIGN uint8_t buf_rsi[128]; /* Input compressed polynomial */

  if (!mlk_sys_check_capability(MLK_SYS_CAP_AVX2))
  {
    fprintf(
        stderr,
        "ABI check poly_decompress_d4_avx2_asm: host lacks AVX2, skipping\n");
    return MLK_ABICHECK_SKIPPED;
  }

  for (test_iter = 0; test_iter < MLK_ABICHECK_NUM_TESTS; test_iter++)
  {
    /* Initialize random register state */
    init_x86_64_register_state(&input_state);

    randombytes(buf_rdi, 512);
    randombytes(buf_rdx, 32);
    randombytes(buf_rsi, 128);

    /* Set up register state for function arguments */
    input_state.rdi = (uint64_t)buf_rdi;
    input_state.rdx = (uint64_t)buf_rdx;
    input_state.rsi = (uint64_t)buf_rsi;

    /* Call function through ABI test stub */
    asm_call_stub_x86_64_sysv(
        &input_state, &output_state,
        (MLK_SYSV_ABI
         void (*)(void))mlk_poly_decompress_d4_avx2_asm);

    /* Check ABI compliance */
    violations = check_x86_64_sysv_compliance(&input_state, &output_state,
                                              MLK_ABICHECK_VERBOSE);
    if (violations > 0)
    {
      fprintf(stderr,
              "ABI test FAILED for poly_decompress_d4_avx2_asm (iteration %d): "
              "%d violations\n",
              test_iter + 1, violations);
      return MLK_ABICHECK_FAILED;
    }
  }

  return MLK_ABICHECK_PASSED;
}

#endif /* MLK_SYS_X86_64 && MLK_SYSV_ABI_SUPPORTED && __AVX2__ */
