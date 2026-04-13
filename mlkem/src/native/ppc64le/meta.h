/*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */

#ifndef MLK_NATIVE_PPC64LE_META_H
#define MLK_NATIVE_PPC64LE_META_H

/* Identifier for this backend so that source and assembly files
 * in the build can be appropriately guarded. */
#define MLK_ARITH_BACKEND_PPC64LE_DEFAULT

#define MLK_ARITH_BACKEND_NAME PPC64LE_DEFAULT

/* Set of primitives that this backend replaces */
#define MLK_USE_NATIVE_NTT
#define MLK_USE_NATIVE_INTT
#define MLK_USE_NATIVE_POLY_REDUCE
#define MLK_USE_NATIVE_POLY_TOMONT

#if !defined(__ASSEMBLER__)
#include <string.h>
#include "../../common.h"
#include "../../params.h"
#include "../api.h"
#include "src/arith_native_ppc64le.h"

#include <sys/auxv.h>

static int mlkem_ppc_check_cap()
{
  static int ppc_inited = 0;
  static int have_cap = 0;

  if (ppc_inited)
  {
    return have_cap;
  }
  have_cap = (getauxval(AT_HWCAP2) & PPC_FEATURE2_ARCH_2_07) ? 1 : 0;
  ppc_inited = 1;
  return have_cap;
}

MLK_MUST_CHECK_RETURN_VALUE
static MLK_INLINE int mlk_ntt_native(int16_t data[MLKEM_N])
{
  if (!mlkem_ppc_check_cap())
  {
    return MLK_NATIVE_FUNC_FALLBACK;
  }
  mlk_ntt_ppc(data, mlk_ppc_qdata);
  return MLK_NATIVE_FUNC_SUCCESS;
}

MLK_MUST_CHECK_RETURN_VALUE
static MLK_INLINE int mlk_intt_native(int16_t data[MLKEM_N])
{
  if (!mlkem_ppc_check_cap())
  {
    return MLK_NATIVE_FUNC_FALLBACK;
  }
  mlk_intt_ppc(data, mlk_ppc_qdata);
  return MLK_NATIVE_FUNC_SUCCESS;
}

MLK_MUST_CHECK_RETURN_VALUE
static MLK_INLINE int mlk_poly_reduce_native(int16_t data[MLKEM_N])
{
  if (!mlkem_ppc_check_cap())
  {
    return MLK_NATIVE_FUNC_FALLBACK;
  }
  mlk_reduce_ppc(data, mlk_ppc_qdata);
  return MLK_NATIVE_FUNC_SUCCESS;
}

MLK_MUST_CHECK_RETURN_VALUE
static MLK_INLINE int mlk_poly_tomont_native(int16_t data[MLKEM_N])
{
  if (!mlkem_ppc_check_cap())
  {
    return MLK_NATIVE_FUNC_FALLBACK;
  }
  mlk_poly_tomont_ppc(data, mlk_ppc_qdata);
  return MLK_NATIVE_FUNC_SUCCESS;
}
#endif /* !__ASSEMBLER__ */

#endif /* !MLK_NATIVE_PPC64LE_META_H */
