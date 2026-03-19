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

#if defined(MLK_SYS_X86_64)

#include <stdio.h>

#include "../notrandombytes/notrandombytes.h"
#include "abicheckutil.h"
#include "checks_all.h"

typedef struct x86_64_register_state reg_state;

#define NUM_TESTS 3

void mlk_polyvec_basemul_acc_montgomery_cached_asm_k4(int16_t *r,
                                                      const int16_t *a,
                                                      const int16_t *b,
                                                      const int16_t *b_cache);

int check_polyvec_basemul_acc_montgomery_cached_asm_k4_x86_64(void)
{
  int test_iter;
  reg_state input_state, output_state;
  int violations;
  MLK_ALIGN uint8_t buf_rcx[1024]; /* Mulcache for b (4 x 128 x int16_t) */
  MLK_ALIGN uint8_t buf_rdi[512];  /* Output polynomial (256 x int16_t) */
  MLK_ALIGN uint8_t buf_rdx[2048]; /* Input polyvec b (4 x 256 x int16_t) */
  MLK_ALIGN uint8_t buf_rsi[2048]; /* Input polyvec a (4 x 256 x int16_t) */

  for (test_iter = 0; test_iter < NUM_TESTS; test_iter++)
  {
    /* Initialize random register state */
    init_x86_64_register_state(&input_state);

    /* Initialize buffer for rcx */
    randombytes(buf_rcx, 1024);
    /* Initialize buffer for rdi */
    randombytes(buf_rdi, 512);
    /* Initialize buffer for rdx */
    randombytes(buf_rdx, 2048);
    /* Initialize buffer for rsi */
    randombytes(buf_rsi, 2048);

    /* Set up register state for function arguments */
    input_state.rcx = (uint64_t)buf_rcx;
    input_state.rdi = (uint64_t)buf_rdi;
    input_state.rdx = (uint64_t)buf_rdx;
    input_state.rsi = (uint64_t)buf_rsi;

    /* Call function through ABI test stub */
    asm_call_stub_x86_64(
        &input_state, &output_state,
        (void (*)(void))mlk_polyvec_basemul_acc_montgomery_cached_asm_k4);

    /* Check ABI compliance */
    violations = check_x86_64_sysv_compliance(&input_state, &output_state);
    if (violations > 0)
    {
      fprintf(
          stderr,
          "ABI test FAILED for polyvec_basemul_acc_montgomery_cached_asm_k4 "
          "(iteration %d): %d violations\n",
          test_iter + 1, violations);
      return 1;
    }
  }

  return 0;
}

#else /* MLK_SYS_X86_64 */

#include "../../mlkem/src/common.h"
MLK_EMPTY_CU(check_polyvec_basemul_acc_montgomery_cached_asm_k4_x86_64)

#endif /* !MLK_SYS_X86_64 */
