/*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */
#ifndef MLK_NATIVE_PPC64LE_SRC_ARITH_NATIVE_PPC64LE_H
#define MLK_NATIVE_PPC64LE_SRC_ARITH_NATIVE_PPC64LE_H

#include <stdint.h>
#include "../../../common.h"
#include "consts.h"

#define mlk_ntt_ppc MLK_NAMESPACE(ntt_ppc)
void mlk_ntt_ppc(int16_t *, const int16_t *);

#define mlk_intt_ppc MLK_NAMESPACE(intt_ppc)
void mlk_intt_ppc(int16_t *, const int16_t *);

#define mlk_reduce_ppc MLK_NAMESPACE(reduce_ppc)
void mlk_reduce_ppc(int16_t *r, const int16_t *);

#define mlk_poly_tomont_ppc MLK_NAMESPACE(poly_tomont_ppc)
void mlk_poly_tomont_ppc(int16_t *, const int16_t *);

#endif /* !MLK_NATIVE_PPC64LE_SRC_ARITH_NATIVE_PPC64LE_H */
