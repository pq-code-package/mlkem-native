/*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */

#ifndef MLK_DEV_PPC64LE_META_H
#define MLK_DEV_PPC64LE_META_H

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

static MLK_INLINE int mlk_ntt_native(int16_t data[MLKEM_N])
{
  mlk_ntt_ppc(data, mlk_ppc_qdata);
  return MLK_NATIVE_FUNC_SUCCESS;
}

static MLK_INLINE int mlk_intt_native(int16_t data[MLKEM_N])
{
  mlk_intt_ppc(data, mlk_ppc_qdata);
  return MLK_NATIVE_FUNC_SUCCESS;
}

static MLK_INLINE int mlk_poly_reduce_native(int16_t data[MLKEM_N])
{
  mlk_reduce_ppc(data, mlk_ppc_qdata);
  return MLK_NATIVE_FUNC_SUCCESS;
}

static MLK_INLINE int mlk_poly_tomont_native(int16_t data[MLKEM_N])
{
  mlk_poly_tomont_ppc(data, mlk_ppc_qdata);
  return MLK_NATIVE_FUNC_SUCCESS;
}
#endif /* !__ASSEMBLER__ */

#endif /* !MLK_DEV_PPC64LE_META_H */
