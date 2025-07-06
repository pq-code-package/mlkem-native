/*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */
#ifndef MLK_NATIVE_RISCV64_SRC_RV64V_SETTINGS_H
#define MLK_NATIVE_RISCV64_SRC_RV64V_SETTINGS_H

/*  === vector configuration */
#ifndef MLK_RVV_VLEN
#define MLK_RVV_VLEN 256
#endif



/*  vl value for a 16-bit wide type */
#define MLK_RVV_E16M1_VL (MLK_RVV_VLEN / 16)

/*  Montgomery reduction constants */
/*  n   = 256; q   = 3329; r   = 2^16 */
/* check-magic: 3327 == unsigned_mod(-pow(MLKEM_Q,-1,2^16), 2^16) */
#define MLKEM_QI 3327

/* check-magic: 2285 == unsigned_mod(2^16, MLKEM_Q) */
#define MLK_MONT_R1 2285

/* check-magic: 1353 == pow(2, 32, MLKEM_Q) */
#define MLK_MONT_R2 1353

/* check-magic: 1441 == pow(2,32-7,MLKEM_Q) */
#define MLK_MONT_NR 1441

#endif /* !MLK_NATIVE_RISCV64_SRC_RV64V_SETTINGS_H */
