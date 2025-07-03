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

/* check-magic: off */

/*  Montgomery reduction constants */
/*  n   = 256; q   = 3329; r   = 2^16 */
/*  qi  = lift(Mod(-q, r)^-1) */
#define MLKEM_QI 3327

/*  r1  = lift(Mod(r, q)) */
#define MLK_MONT_R1 2285

/*  r2  = lift(Mod(r, q)^2) */
#define MLK_MONT_R2 1353

/*  in  = lift(Mod(n / 2, q)^-1) */
/*  nr  = (in * r^2) % q */
#define MLK_MONT_NR 1441

/* check-magic: on */

#endif /* !MLK_NATIVE_RISCV64_SRC_RV64V_SETTINGS_H */
