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
#include "checks_x86_64_all.h"

#if defined(MLK_SYS_X86_64) && defined(MLK_SYSV_ABI_SUPPORTED)

#include "../../notrandombytes/notrandombytes.h"

typedef struct x86_64_register_state reg_state;

MLK_SYSV_ABI
void mlk_poly_compress_d10_avx2_asm(uint8_t *r, const int16_t *a,
                                    const uint8_t *data);

int check_poly_compress_d10_avx2_asm(void)
{
  int test_iter;
  reg_state input_state, output_state;
  int violations;
  MLK_ALIGN uint8_t buf_rdi[320]; /* Output compressed polynomial */
  MLK_ALIGN uint8_t buf_rdx[32];  /* Precomputed compression constants */
  MLK_ALIGN uint8_t buf_rsi[512]; /* Input polynomial (256 x int16_t) */

  if (!mlk_sys_check_capability(MLK_SYS_CAP_AVX2))
  {
    fprintf(
        stderr,
        "ABI check poly_compress_d10_avx2_asm: host lacks AVX2, skipping\n");
    return MLK_ABICHECK_SKIPPED;
  }

  for (test_iter = 0; test_iter < MLK_ABICHECK_NUM_TESTS; test_iter++)
  {
    /* Initialize random register state */
    init_x86_64_register_state(&input_state);

    randombytes(buf_rdi, 320);
    randombytes(buf_rdx, 32);
    randombytes(buf_rsi, 512);

    /* Set up register state for function arguments */
    input_state.rdi = (uint64_t)buf_rdi;
    input_state.rdx = (uint64_t)buf_rdx;
    input_state.rsi = (uint64_t)buf_rsi;

    /* Call function through ABI test stub */
    asm_call_stub_x86_64_sysv(
        &input_state, &output_state,
        (MLK_SYSV_ABI
         void (*)(void))mlk_poly_compress_d10_avx2_asm);

    /* Check ABI compliance */
    violations = check_x86_64_sysv_compliance(&input_state, &output_state,
                                              MLK_ABICHECK_VERBOSE);
    if (violations > 0)
    {
      fprintf(stderr,
              "ABI test FAILED for poly_compress_d10_avx2_asm (iteration %d): "
              "%d violations\n",
              test_iter + 1, violations);
      return MLK_ABICHECK_FAILED;
    }
  }

  return MLK_ABICHECK_PASSED;
}

#else /* MLK_SYS_X86_64 && MLK_SYSV_ABI_SUPPORTED */

int check_poly_compress_d10_avx2_asm(void)
{
  fprintf(stderr,
          "ABI check poly_compress_d10_avx2_asm: unsupported architecture\n");
  return MLK_ABICHECK_FAILED;
}

#endif /* !(MLK_SYS_X86_64 && MLK_SYSV_ABI_SUPPORTED) */
