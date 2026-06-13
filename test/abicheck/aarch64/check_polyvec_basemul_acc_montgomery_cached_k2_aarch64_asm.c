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

#if defined(MLK_SYS_AARCH64)

#include "../../notrandombytes/notrandombytes.h"

typedef struct register_state reg_state;

void mlk_polyvec_basemul_acc_montgomery_cached_k2_aarch64_asm(
    int16_t r[256], const int16_t a[512], const int16_t b[512],
    const int16_t b_cache[256]);

int check_polyvec_basemul_acc_montgomery_cached_k2_aarch64_asm(void)
{
  int test_iter;
  reg_state input_state, output_state;
  int violations;
  MLK_ALIGN uint8_t buf_x0[512];  /* Output polynomial */
  MLK_ALIGN uint8_t buf_x1[1024]; /* Input polynomial vector a */
  MLK_ALIGN uint8_t buf_x2[1024]; /* Input polynomial vector b */
  MLK_ALIGN uint8_t buf_x3[512];  /* Cached values for b */

  for (test_iter = 0; test_iter < MLK_ABICHECK_NUM_TESTS; test_iter++)
  {
    /* Initialize random register state */
    init_register_state(&input_state);

    randombytes(buf_x0, 512);
    randombytes(buf_x1, 1024);
    randombytes(buf_x2, 1024);
    randombytes(buf_x3, 512);

    /* Set up register state for function arguments */
    input_state.gpr[0] = (uint64_t)buf_x0;
    input_state.gpr[1] = (uint64_t)buf_x1;
    input_state.gpr[2] = (uint64_t)buf_x2;
    input_state.gpr[3] = (uint64_t)buf_x3;

    /* Call function through ABI test stub */
    asm_call_stub_aarch64(
        &input_state, &output_state,
        (void (*)(
            void))mlk_polyvec_basemul_acc_montgomery_cached_k2_aarch64_asm);

    /* Check ABI compliance */
    violations = check_aarch64_aapcs_compliance(&input_state, &output_state,
                                                MLK_ABICHECK_VERBOSE);
    if (violations > 0)
    {
      fprintf(stderr,
              "ABI test FAILED for "
              "polyvec_basemul_acc_montgomery_cached_k2_aarch64_asm (iteration "
              "%d): %d violations\n",
              test_iter + 1, violations);
      return MLK_ABICHECK_FAILED;
    }
  }

  return MLK_ABICHECK_PASSED;
}

#else /* MLK_SYS_AARCH64 */

int check_polyvec_basemul_acc_montgomery_cached_k2_aarch64_asm(void)
{
  fprintf(stderr,
          "ABI check polyvec_basemul_acc_montgomery_cached_k2_aarch64_asm: "
          "unsupported architecture\n");
  return MLK_ABICHECK_FAILED;
}

#endif /* !MLK_SYS_AARCH64 */
