/*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */

#ifndef MLK_FIPS202_NATIVE_X86_64_KECCAK_F1600_X1_AVX512_H
#define MLK_FIPS202_NATIVE_X86_64_KECCAK_F1600_X1_AVX512_H

#include "../../../common.h"

#if !defined(MLK_SYS_X86_64_AVX512)
#error This backend can only be used if AVX-512 (F, VL and DQ) is enabled.
#endif

/* Guard for assembly file */
#define MLK_FIPS202_X86_64_NEED_X1_AVX512

/* Part of backend API */
#define MLK_USE_NATIVE_FIPS202_X1

#if !defined(__ASSEMBLER__)
#include "../api.h"
#include "src/fips202_native_x86_64.h"
MLK_MUST_CHECK_RETURN_VALUE
static MLK_INLINE int mlk_keccak_f1600_x1_native(uint64_t *state)
{
  if (!mlk_sys_check_capability(MLK_SYS_CAP_X86_64_AVX512))
  {
    return MLK_NATIVE_FUNC_FALLBACK;
  }

  mlk_keccak_f1600_x1_avx512_asm(state, mlk_keccakf1600_round_constants);
  return MLK_NATIVE_FUNC_SUCCESS;
}
#endif /* !__ASSEMBLER__ */

#endif /* !MLK_FIPS202_NATIVE_X86_64_KECCAK_F1600_X1_AVX512_H */
