/*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */

#ifndef MLK_FIPS202_NATIVE_ARMV81M_MVE_H
#define MLK_FIPS202_NATIVE_ARMV81M_MVE_H

#define MLK_FIPS202_NATIVE_ARMV81M

/* Part of backend API */
#define MLK_USE_FIPS202_X1_NATIVE
#define MLK_USE_FIPS202_X4_NATIVE
/* Guard for assembly files */
#define MLK_FIPS202_ARMV81M_NEED_X1
#define MLK_FIPS202_ARMV81M_NEED_X4

#if !defined(__ASSEMBLER__)
#include <stdint.h>
#include "../api.h"

#define mlk_keccak_f1600_x1_native_impl \
  MLK_NAMESPACE(keccak_f1600_x1_native_impl)
int mlk_keccak_f1600_x1_native_impl(uint64_t *state);

MLK_MUST_CHECK_RETURN_VALUE
static MLK_INLINE int mlk_keccak_f1600_x1_native(uint64_t *state)
{
  return mlk_keccak_f1600_x1_native_impl(state);
}

#define mlk_keccak_f1600_x4_native_impl \
  MLK_NAMESPACE(keccak_f1600_x4_native_impl)
int mlk_keccak_f1600_x4_native_impl(uint64_t *state);

MLK_MUST_CHECK_RETURN_VALUE
static MLK_INLINE int mlk_keccak_f1600_x4_native(uint64_t *state)
{
  return mlk_keccak_f1600_x4_native_impl(state);
}

#endif /* !__ASSEMBLER__ */

#endif /* !MLK_FIPS202_NATIVE_ARMV81M_MVE_H */
