/*
 * Copyright (c) 2024 The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0
 */

/*
 * WARNING: This file is auto-generated from scripts/autogenerate_files.py
 *          Do not modify it directly.
 */

/*
 * Monolithic compilation unit bundling all compilation units within
 * mlkem-native
 */

#include "mlkem/cbd.c"
#include "mlkem/debug/debug.c"
#include "mlkem/fips202/fips202.c"
#include "mlkem/fips202/fips202x4.c"
#include "mlkem/fips202/keccakf1600.c"
#include "mlkem/fips202/native/aarch64/src/keccakf1600_round_constants.c"
#include "mlkem/fips202/native/x86_64/src/KeccakP-1600-times4-SIMD256.c"
#include "mlkem/indcpa.c"
#include "mlkem/kem.c"
#include "mlkem/native/aarch64/src/aarch64_zetas.c"
#include "mlkem/native/aarch64/src/rej_uniform_table.c"
#include "mlkem/native/x86_64/src/basemul.c"
#include "mlkem/native/x86_64/src/consts.c"
#include "mlkem/native/x86_64/src/rej_uniform_avx2.c"
#include "mlkem/native/x86_64/src/rej_uniform_table.c"
#include "mlkem/ntt.c"
#include "mlkem/poly.c"
#include "mlkem/polyvec.c"
#include "mlkem/rej_uniform.c"
#include "mlkem/verify.c"
#include "mlkem/zetas.c"
