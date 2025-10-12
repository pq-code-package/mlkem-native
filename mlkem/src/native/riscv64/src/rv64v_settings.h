/*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */
#ifndef MLK_NATIVE_RISCV64_SRC_RV64V_SETTINGS_H
#define MLK_NATIVE_RISCV64_SRC_RV64V_SETTINGS_H

#include <riscv_vector.h>

/*  === vector configuration */
#ifndef MLK_RVV_VLEN
#define MLK_RVV_VLEN 256
#endif

/*  vl value for a 16-bit wide type */
#define MLK_RVV_E16M1_VL (MLK_RVV_VLEN / 16)

#endif /* !MLK_NATIVE_RISCV64_SRC_RV64V_SETTINGS_H */
