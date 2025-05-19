/*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */

/*  === Kyber NTT using RISC-V Vector intrinstics */

#include "../../../common.h"

#if defined(MLK_ARITH_BACKEND_RISCV64)

#include <riscv_vector.h>
#include "arith_native_riscv64.h"
#include "rv64v_settings.h"

#ifndef MLK_RVV_WIDENING_MUL
static inline vint16m1_t fq_redc(vint16m1_t rh, vint16m1_t rl, size_t vl)
{
  vint16m1_t t;
  vbool16_t c;

  t = __riscv_vmul_vx_i16m1(rl, MLKEM_QI, vl); /* t = l * -Q^-1  */
  t = __riscv_vmulh_vx_i16m1(t, MLKEM_Q, vl);  /* t = (t*Q) / R  */
  c = __riscv_vmsne_vx_i16m1_b16(rl, 0, vl);   /* c = l == 0     */
  t = __riscv_vadc_vvm_i16m1(t, rh, c, vl);    /* t += h + c     */

  return t;
}
#endif /* !MLK_RVV_WIDENING_MUL */

/*  Narrowing reduction */

static inline vint16m1_t fq_redc2(vint32m2_t z, size_t vl)
{
  vint16m1_t t;

  t = __riscv_vmul_vx_i16m1(__riscv_vncvt_x_x_w_i16m1(z, vl), MLKEM_QI,
                            vl); /*    t = l * -Q^-1 */
  z = __riscv_vadd_vv_i32m2(z, __riscv_vwmul_vx_i32m2(t, MLKEM_Q, vl),
                            vl); /*    x = (x + (t*Q)) */
  t = __riscv_vnsra_wx_i16m1(z, 16, vl);

  return t;
}

/*  Narrowing Barrett (per original Kyber)  */

static inline vint16m1_t fq_barrett(vint16m1_t a, size_t vl)
{
  vint16m1_t t;
  const int16_t v = ((1 << 26) + MLKEM_Q / 2) / MLKEM_Q;

  t = __riscv_vmulh_vx_i16m1(a, v, vl);
  t = __riscv_vadd_vx_i16m1(t, 1 << (25 - 16), vl);
  t = __riscv_vsra_vx_i16m1(t, 26 - 16, vl);
  t = __riscv_vmul_vx_i16m1(t, MLKEM_Q, vl);
  t = __riscv_vsub_vv_i16m1(a, t, vl);

  return t;
}

/*  Conditionally add Q (if negative) */

static inline vint16m1_t fq_cadd(vint16m1_t rx, size_t vl)
{
  vbool16_t bn;

  bn = __riscv_vmslt_vx_i16m1_b16(rx, 0, vl);             /*   if x < 0:   */
  rx = __riscv_vadd_vx_i16m1_mu(bn, rx, rx, MLKEM_Q, vl); /*     x += Q    */
  return rx;
}

/*  Conditionally subtract Q (if Q or above) */

static inline vint16m1_t fq_csub(vint16m1_t rx, size_t vl)
{
  vbool16_t bn;

  bn = __riscv_vmsge_vx_i16m1_b16(rx, MLKEM_Q, vl);       /*   if x >= 0:  */
  rx = __riscv_vsub_vx_i16m1_mu(bn, rx, rx, MLKEM_Q, vl); /*     x -= Q    */
  return rx;
}

/*  Montgomery multiply: vector-vector  */

static inline vint16m1_t fq_mul_vv(vint16m1_t rx, vint16m1_t ry, size_t vl)
{
#ifndef MLK_RVV_WIDENING_MUL
  vint16m1_t rl, rh;

  rh = __riscv_vmulh_vv_i16m1(rx, ry, vl); /*  h = (x * y) / R */
  rl = __riscv_vmul_vv_i16m1(rx, ry, vl);  /*  l = (x * y) % R */
  return fq_redc(rh, rl, vl);
#else  /* !MLK_RVV_WIDENING_MUL */
  return fq_redc2(__riscv_vwmul_vv_i32m2(rx, ry, vl), vl);
#endif /* MLK_RVV_WIDENING_MUL */
}

/*  Montgomery multiply: vector-scalar  */

static inline vint16m1_t fq_mul_vx(vint16m1_t rx, int16_t ry, size_t vl)
{
#ifndef MLK_RVV_WIDENING_MUL
  vint16m1_t rl, rh;

  rh = __riscv_vmulh_vx_i16m1(rx, ry, vl); /*  h = (x * y) / R */
  rl = __riscv_vmul_vx_i16m1(rx, ry, vl);  /*  l = (x * y) % R */
  return fq_redc(rh, rl, vl);
#else  /* !MLK_RVV_WIDENING_MUL */
  return fq_redc2(__riscv_vwmul_vx_i32m2(rx, ry, vl), vl);
#endif /* MLK_RVV_WIDENING_MUL */
}

/*  full normalization  */

static inline vint16m1_t fq_mulq_vx(vint16m1_t rx, int16_t ry, size_t vl)
{
  return fq_cadd(fq_mul_vx(rx, ry, vl), vl);
}

/*  create a permutation for swapping index bits a and b, a < b */

static vuint16m2_t bitswap_perm(unsigned a, unsigned b, size_t vl)
{
  const vuint16m2_t v2id = __riscv_vid_v_u16m2(vl);

  vuint16m2_t xa, xb;
  xa = __riscv_vsrl_vx_u16m2(v2id, b - a, vl);
  xa = __riscv_vxor_vv_u16m2(xa, v2id, vl);
  xa = __riscv_vand_vx_u16m2(xa, (1 << a), vl);
  xb = __riscv_vsll_vx_u16m2(xa, b - a, vl);
  xa = __riscv_vxor_vv_u16m2(xa, xb, vl);
  xa = __riscv_vxor_vv_u16m2(v2id, xa, vl);
  return xa;
}

/*  NOTE: NTT is currently fixed for vlen==256  */

#if (MLK_RVV_VLEN == 256)

/*************************************************
 * Name:        poly_ntt
 *
 * Description: Computes negacyclic number-theoretic transform (NTT) of
 *              a polynomial in place;
 *              inputs assumed to be in normal order, output in
 *bitreversed order
 *
 * Arguments:   - uint16_t *r: pointer to in/output polynomial
 **************************************************/

/*  forward butterfly operation */

#define MLK_RVV_BFLY_FX(u0, u1, ut, uc, vl) \
  {                                         \
    ut = fq_mul_vx(u1, uc, vl);             \
    u1 = __riscv_vsub_vv_i16m1(u0, ut, vl); \
    u0 = __riscv_vadd_vv_i16m1(u0, ut, vl); \
  }

#define MLK_RVV_BFLY_FV(u0, u1, ut, uc, vl) \
  {                                         \
    ut = fq_mul_vv(u1, uc, vl);             \
    u1 = __riscv_vsub_vv_i16m1(u0, ut, vl); \
    u0 = __riscv_vadd_vv_i16m1(u0, ut, vl); \
  }

static vint16m2_t mlk_rv64v_ntt2(vint16m2_t vp, vint16m1_t cz)
{
  size_t vl = MLK_RVV_E16M1_VL;
  size_t vl2 = 2 * vl;

  const vuint16m2_t v2p8 = bitswap_perm(3, 4, vl2);
  const vuint16m2_t v2p4 = bitswap_perm(2, 4, vl2);
  const vuint16m2_t v2p2 = bitswap_perm(1, 4, vl2);

  /*    p1 = p8(p4(p2)) */
  const vuint16m2_t v2p1 = __riscv_vrgather_vv_u16m2(
      __riscv_vrgather_vv_u16m2(v2p2, v2p4, vl2), v2p8, vl2);

  const vuint16m1_t vid = __riscv_vid_v_u16m1(vl);
  const vuint16m1_t cs8 =
      __riscv_vadd_vx_u16m1(__riscv_vsrl_vx_u16m1(vid, 3, vl), 2, vl);
  const vuint16m1_t cs4 =
      __riscv_vadd_vx_u16m1(__riscv_vsrl_vx_u16m1(vid, 2, vl), 2 + 2, vl);
  const vuint16m1_t cs2 =
      __riscv_vadd_vx_u16m1(__riscv_vsrl_vx_u16m1(vid, 1, vl), 2 + 2 + 4, vl);

  vint16m1_t vt, c0, t0, t1;

  /*    swap 8  */
  vp = __riscv_vrgatherei16_vv_i16m2(vp, v2p8, vl2);
  t0 = __riscv_vget_v_i16m2_i16m1(vp, 0);
  t1 = __riscv_vget_v_i16m2_i16m1(vp, 1);

  c0 = __riscv_vrgather_vv_i16m1(cz, cs8, vl);
  MLK_RVV_BFLY_FV(t0, t1, vt, c0, vl);

  /*    swap 4  */
  vp = __riscv_vcreate_v_i16m1_i16m2(t0, t1);
  vp = __riscv_vrgatherei16_vv_i16m2(vp, v2p4, vl2);
  t0 = __riscv_vget_v_i16m2_i16m1(vp, 0);
  t1 = __riscv_vget_v_i16m2_i16m1(vp, 1);

  c0 = __riscv_vrgather_vv_i16m1(cz, cs4, vl);
  MLK_RVV_BFLY_FV(t0, t1, vt, c0, vl);

  /*    swap 2  */
  vp = __riscv_vcreate_v_i16m1_i16m2(t0, t1);
  vp = __riscv_vrgatherei16_vv_i16m2(vp, v2p2, vl2);
  t0 = __riscv_vget_v_i16m2_i16m1(vp, 0);
  t1 = __riscv_vget_v_i16m2_i16m1(vp, 1);

  c0 = __riscv_vrgather_vv_i16m1(cz, cs2, vl);
  MLK_RVV_BFLY_FV(t0, t1, vt, c0, vl);

  /*    normalize   */
  t0 = fq_mulq_vx(t0, MLK_MONT_R1, vl);
  t1 = fq_mulq_vx(t1, MLK_MONT_R1, vl);

  /*    reorganize  */
  vp = __riscv_vcreate_v_i16m1_i16m2(t0, t1);
  vp = __riscv_vrgatherei16_vv_i16m2(vp, v2p1, vl2);

  return vp;
}

void mlk_rv64v_poly_ntt(int16_t *r)
{
  /* zetas can be compiled into vector constants; don't pass as a pointer */
  /* check-magic: off */
  const int16_t zeta[0x80] = {
      -1044, -758,  573,   -1325, 1223,  652,   -552,  1015,  -1103, 430,
      555,   843,   -1251, 871,   1550,  105,   -359,  -1517, 264,   383,
      -1293, 1491,  -282,  -1544, 422,   587,   177,   -235,  -291,  -460,
      1574,  1653,  1493,  1422,  -829,  1458,  516,   -8,    -320,  -666,
      -246,  778,   1159,  -147,  -777,  1483,  -602,  1119,  287,   202,
      -1602, -130,  -1618, -1162, 126,   1469,  -1590, 644,   -872,  349,
      418,   329,   -156,  -75,   -171,  622,   -681,  1017,  -853,  -90,
      -271,  830,   817,   1097,  603,   610,   1322,  -1285, -1465, 384,
      1577,  182,   732,   608,   107,   -1421, -247,  -951,  -1215, -136,
      1218,  -1335, -874,  220,   -1187, -1659, 962,   -1202, -1542, 411,
      -398,  961,   -1508, -725,  -1185, -1530, -1278, 794,   -1510, -854,
      -870,  478,   -1474, 1468,  -205,  -1571, 448,   -1065, 677,   -1275,
      -108,  -308,  996,   991,   958,   -1460, 1522,  1628,
  };
  /* check-magic: on */

  size_t vl = MLK_RVV_E16M1_VL;
  size_t vl2 = 2 * vl;

  vint16m1_t vt;
  vint16m1_t v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, va, vb, vc, vd, ve, vf;

  const vint16m1_t z0 = __riscv_vle16_v_i16m1(&zeta[0x00], vl);
  const vint16m1_t z2 = __riscv_vle16_v_i16m1(&zeta[0x10], vl);
  const vint16m1_t z4 = __riscv_vle16_v_i16m1(&zeta[0x20], vl);
  const vint16m1_t z6 = __riscv_vle16_v_i16m1(&zeta[0x30], vl);
  const vint16m1_t z8 = __riscv_vle16_v_i16m1(&zeta[0x40], vl);
  const vint16m1_t za = __riscv_vle16_v_i16m1(&zeta[0x50], vl);
  const vint16m1_t zc = __riscv_vle16_v_i16m1(&zeta[0x60], vl);
  const vint16m1_t ze = __riscv_vle16_v_i16m1(&zeta[0x70], vl);

  v0 = __riscv_vle16_v_i16m1(&r[0x00], vl);
  v1 = __riscv_vle16_v_i16m1(&r[0x10], vl);
  v2 = __riscv_vle16_v_i16m1(&r[0x20], vl);
  v3 = __riscv_vle16_v_i16m1(&r[0x30], vl);
  v4 = __riscv_vle16_v_i16m1(&r[0x40], vl);
  v5 = __riscv_vle16_v_i16m1(&r[0x50], vl);
  v6 = __riscv_vle16_v_i16m1(&r[0x60], vl);
  v7 = __riscv_vle16_v_i16m1(&r[0x70], vl);
  v8 = __riscv_vle16_v_i16m1(&r[0x80], vl);
  v9 = __riscv_vle16_v_i16m1(&r[0x90], vl);
  va = __riscv_vle16_v_i16m1(&r[0xa0], vl);
  vb = __riscv_vle16_v_i16m1(&r[0xb0], vl);
  vc = __riscv_vle16_v_i16m1(&r[0xc0], vl);
  vd = __riscv_vle16_v_i16m1(&r[0xd0], vl);
  ve = __riscv_vle16_v_i16m1(&r[0xe0], vl);
  vf = __riscv_vle16_v_i16m1(&r[0xf0], vl);

  MLK_RVV_BFLY_FX(v0, v8, vt, zeta[0x01], vl);
  MLK_RVV_BFLY_FX(v1, v9, vt, zeta[0x01], vl);
  MLK_RVV_BFLY_FX(v2, va, vt, zeta[0x01], vl);
  MLK_RVV_BFLY_FX(v3, vb, vt, zeta[0x01], vl);
  MLK_RVV_BFLY_FX(v4, vc, vt, zeta[0x01], vl);
  MLK_RVV_BFLY_FX(v5, vd, vt, zeta[0x01], vl);
  MLK_RVV_BFLY_FX(v6, ve, vt, zeta[0x01], vl);
  MLK_RVV_BFLY_FX(v7, vf, vt, zeta[0x01], vl);

  MLK_RVV_BFLY_FX(v0, v4, vt, zeta[0x10], vl);
  MLK_RVV_BFLY_FX(v1, v5, vt, zeta[0x10], vl);
  MLK_RVV_BFLY_FX(v2, v6, vt, zeta[0x10], vl);
  MLK_RVV_BFLY_FX(v3, v7, vt, zeta[0x10], vl);
  MLK_RVV_BFLY_FX(v8, vc, vt, zeta[0x11], vl);
  MLK_RVV_BFLY_FX(v9, vd, vt, zeta[0x11], vl);
  MLK_RVV_BFLY_FX(va, ve, vt, zeta[0x11], vl);
  MLK_RVV_BFLY_FX(vb, vf, vt, zeta[0x11], vl);

  MLK_RVV_BFLY_FX(v0, v2, vt, zeta[0x20], vl);
  MLK_RVV_BFLY_FX(v1, v3, vt, zeta[0x20], vl);
  MLK_RVV_BFLY_FX(v4, v6, vt, zeta[0x21], vl);
  MLK_RVV_BFLY_FX(v5, v7, vt, zeta[0x21], vl);
  MLK_RVV_BFLY_FX(v8, va, vt, zeta[0x30], vl);
  MLK_RVV_BFLY_FX(v9, vb, vt, zeta[0x30], vl);
  MLK_RVV_BFLY_FX(vc, ve, vt, zeta[0x31], vl);
  MLK_RVV_BFLY_FX(vd, vf, vt, zeta[0x31], vl);

  MLK_RVV_BFLY_FX(v0, v1, vt, zeta[0x40], vl);
  MLK_RVV_BFLY_FX(v2, v3, vt, zeta[0x41], vl);
  MLK_RVV_BFLY_FX(v4, v5, vt, zeta[0x50], vl);
  MLK_RVV_BFLY_FX(v6, v7, vt, zeta[0x51], vl);
  MLK_RVV_BFLY_FX(v8, v9, vt, zeta[0x60], vl);
  MLK_RVV_BFLY_FX(va, vb, vt, zeta[0x61], vl);
  MLK_RVV_BFLY_FX(vc, vd, vt, zeta[0x70], vl);
  MLK_RVV_BFLY_FX(ve, vf, vt, zeta[0x71], vl);

  __riscv_vse16_v_i16m2(
      &r[0x00], mlk_rv64v_ntt2(__riscv_vcreate_v_i16m1_i16m2(v0, v1), z0), vl2);
  __riscv_vse16_v_i16m2(
      &r[0x20], mlk_rv64v_ntt2(__riscv_vcreate_v_i16m1_i16m2(v2, v3), z2), vl2);
  __riscv_vse16_v_i16m2(
      &r[0x40], mlk_rv64v_ntt2(__riscv_vcreate_v_i16m1_i16m2(v4, v5), z4), vl2);
  __riscv_vse16_v_i16m2(
      &r[0x60], mlk_rv64v_ntt2(__riscv_vcreate_v_i16m1_i16m2(v6, v7), z6), vl2);
  __riscv_vse16_v_i16m2(
      &r[0x80], mlk_rv64v_ntt2(__riscv_vcreate_v_i16m1_i16m2(v8, v9), z8), vl2);
  __riscv_vse16_v_i16m2(
      &r[0xa0], mlk_rv64v_ntt2(__riscv_vcreate_v_i16m1_i16m2(va, vb), za), vl2);
  __riscv_vse16_v_i16m2(
      &r[0xc0], mlk_rv64v_ntt2(__riscv_vcreate_v_i16m1_i16m2(vc, vd), zc), vl2);
  __riscv_vse16_v_i16m2(
      &r[0xe0], mlk_rv64v_ntt2(__riscv_vcreate_v_i16m1_i16m2(ve, vf), ze), vl2);
}

#undef MLK_RVV_BFLY_FX
#undef MLK_RVV_BFLY_FV

/*************************************************
 * Name:        poly_invntt_tomont
 *
 * Description: Computes inverse of negacyclic number-theoretic transform (NTT)
 *              of a polynomial in place;
 *              inputs assumed to be in bitreversed order,
 *output in normal order
 *
 * Arguments:   - uint16_t *r: pointer to in/output polynomial
 **************************************************/

/*  reverse butterfly operation */

#define MLK_RVV_BFLY_RX(u0, u1, ut, uc, vl) \
  {                                         \
    ut = __riscv_vsub_vv_i16m1(u0, u1, vl); \
    u0 = __riscv_vadd_vv_i16m1(u0, u1, vl); \
    u0 = fq_csub(u0, vl);                   \
    u1 = fq_mul_vx(ut, uc, vl);             \
  }

#define MLK_RVV_BFLY_RV(u0, u1, ut, uc, vl) \
  {                                         \
    ut = __riscv_vsub_vv_i16m1(u0, u1, vl); \
    u0 = __riscv_vadd_vv_i16m1(u0, u1, vl); \
    u0 = fq_csub(u0, vl);                   \
    u1 = fq_mul_vv(ut, uc, vl);             \
  }

static vint16m2_t mlk_rv64v_intt2(vint16m2_t vp, vint16m1_t cz)
{
  size_t vl = MLK_RVV_E16M1_VL;
  size_t vl2 = 2 * vl;

  const vuint16m2_t v2p8 = bitswap_perm(3, 4, vl2);
  const vuint16m2_t v2p4 = bitswap_perm(2, 4, vl2);
  const vuint16m2_t v2p2 = bitswap_perm(1, 4, vl2);

  /*    p0 = p2(p4(p8)) */
  const vuint16m2_t v2p0 = __riscv_vrgather_vv_u16m2(
      __riscv_vrgather_vv_u16m2(v2p8, v2p4, vl2), v2p2, vl2);

  const vuint16m1_t vid = __riscv_vid_v_u16m1(vl);
  const vuint16m1_t cs8 =
      __riscv_vadd_vx_u16m1(__riscv_vsrl_vx_u16m1(vid, 3, vl), 2, vl);
  const vuint16m1_t cs4 =
      __riscv_vadd_vx_u16m1(__riscv_vsrl_vx_u16m1(vid, 2, vl), 2 + 2, vl);
  const vuint16m1_t cs2 =
      __riscv_vadd_vx_u16m1(__riscv_vsrl_vx_u16m1(vid, 1, vl), 2 + 2 + 4, vl);

  vint16m1_t t0, t1, c0, vt;

  /*    initial permute */
  vp = __riscv_vrgatherei16_vv_i16m2(vp, v2p0, vl2);
  t0 = __riscv_vget_v_i16m2_i16m1(vp, 0);
  t1 = __riscv_vget_v_i16m2_i16m1(vp, 1);
  c0 = __riscv_vrgather_vv_i16m1(cz, cs2, vl);
  MLK_RVV_BFLY_RV(t0, t1, vt, c0, vl);

  /*    swap 2  */
  vp = __riscv_vcreate_v_i16m1_i16m2(t0, t1);
  vp = __riscv_vrgatherei16_vv_i16m2(vp, v2p2, vl2);
  t0 = __riscv_vget_v_i16m2_i16m1(vp, 0);
  t1 = __riscv_vget_v_i16m2_i16m1(vp, 1);
  c0 = __riscv_vrgather_vv_i16m1(cz, cs4, vl);
  MLK_RVV_BFLY_RV(t0, t1, vt, c0, vl);

  /*    swap 4  */
  vp = __riscv_vcreate_v_i16m1_i16m2(t0, t1);
  vp = __riscv_vrgatherei16_vv_i16m2(vp, v2p4, vl2);
  t0 = __riscv_vget_v_i16m2_i16m1(vp, 0);
  t1 = __riscv_vget_v_i16m2_i16m1(vp, 1);
  c0 = __riscv_vrgather_vv_i16m1(cz, cs8, vl);
  MLK_RVV_BFLY_RV(t0, t1, vt, c0, vl);

  /*    swap 8  */
  vp = __riscv_vcreate_v_i16m1_i16m2(t0, t1);
  vp = __riscv_vrgatherei16_vv_i16m2(vp, v2p8, vl2);
  t0 = __riscv_vget_v_i16m2_i16m1(vp, 0);
  t1 = __riscv_vget_v_i16m2_i16m1(vp, 1);

  /*    normalize   */
  t0 = fq_mulq_vx(t0, MLK_MONT_R1, vl);
  t1 = fq_mulq_vx(t1, MLK_MONT_R1, vl);

  vp = __riscv_vcreate_v_i16m1_i16m2(t0, t1);

  return vp;
}

void mlk_rv64v_poly_invntt_tomont(int16_t *r)
{
  /* zetas can be compiled into vector constants; don't pass as a pointer */
  /* check-magic: off */
  const int16_t izeta[0x80] = {
      -1044, 758,   1571,  205,   1275,  -677,  1065,  -448,  -1628, -1522,
      1460,  -958,  -991,  -996,  308,   108,   1517,  359,   -411,  1542,
      725,   1508,  -961,  398,   -478,  870,   854,   1510,  -794,  1278,
      1530,  1185,  -202,  -287,  -608,  -732,  951,   247,   1421,  -107,
      1659,  1187,  -220,  874,   1335,  -1218, 136,   1215,  -1422, -1493,
      -1017, 681,   -830,  271,   90,    853,   -384,  1465,  1285,  -1322,
      -610,  -603,  -1097, -817,  -1468, 1474,  130,   1602,  -1469, -126,
      1162,  1618,  75,    156,   -329,  -418,  -349,  872,   -644,  1590,
      1202,  -962,  -1458, 829,   666,   320,   8,     -516,  -1119, 602,
      -1483, 777,   147,   -1159, -778,  246,   -182,  -1577, -383,  -264,
      1544,  282,   -1491, 1293,  -1653, -1574, 460,   291,   235,   -177,
      -587,  -422,  -622,  171,   1325,  -573,  -1015, 552,   -652,  -1223,
      -105,  -1550, -871,  1251,  -843,  -555,  -430,  1103,
  };
  /* check-magic: on */

  size_t vl = MLK_RVV_E16M1_VL;
  size_t vl2 = 2 * vl;

  const vint16m1_t z0 = __riscv_vle16_v_i16m1(&izeta[0x00], vl);
  const vint16m1_t z2 = __riscv_vle16_v_i16m1(&izeta[0x10], vl);
  const vint16m1_t z4 = __riscv_vle16_v_i16m1(&izeta[0x20], vl);
  const vint16m1_t z6 = __riscv_vle16_v_i16m1(&izeta[0x30], vl);
  const vint16m1_t z8 = __riscv_vle16_v_i16m1(&izeta[0x40], vl);
  const vint16m1_t za = __riscv_vle16_v_i16m1(&izeta[0x50], vl);
  const vint16m1_t zc = __riscv_vle16_v_i16m1(&izeta[0x60], vl);
  const vint16m1_t ze = __riscv_vle16_v_i16m1(&izeta[0x70], vl);

  vint16m1_t vt;
  vint16m1_t v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, va, vb, vc, vd, ve, vf;
  vint16m2_t vp;

  vp = mlk_rv64v_intt2(__riscv_vle16_v_i16m2(&r[0x00], vl2), z0);
  v0 = __riscv_vget_v_i16m2_i16m1(vp, 0);
  v1 = __riscv_vget_v_i16m2_i16m1(vp, 1);

  vp = mlk_rv64v_intt2(__riscv_vle16_v_i16m2(&r[0x20], vl2), z2);
  v2 = __riscv_vget_v_i16m2_i16m1(vp, 0);
  v3 = __riscv_vget_v_i16m2_i16m1(vp, 1);

  vp = mlk_rv64v_intt2(__riscv_vle16_v_i16m2(&r[0x40], vl2), z4);
  v4 = __riscv_vget_v_i16m2_i16m1(vp, 0);
  v5 = __riscv_vget_v_i16m2_i16m1(vp, 1);

  vp = mlk_rv64v_intt2(__riscv_vle16_v_i16m2(&r[0x60], vl2), z6);
  v6 = __riscv_vget_v_i16m2_i16m1(vp, 0);
  v7 = __riscv_vget_v_i16m2_i16m1(vp, 1);

  vp = mlk_rv64v_intt2(__riscv_vle16_v_i16m2(&r[0x80], vl2), z8);
  v8 = __riscv_vget_v_i16m2_i16m1(vp, 0);
  v9 = __riscv_vget_v_i16m2_i16m1(vp, 1);

  vp = mlk_rv64v_intt2(__riscv_vle16_v_i16m2(&r[0xa0], vl2), za);
  va = __riscv_vget_v_i16m2_i16m1(vp, 0);
  vb = __riscv_vget_v_i16m2_i16m1(vp, 1);

  vp = mlk_rv64v_intt2(__riscv_vle16_v_i16m2(&r[0xc0], vl2), zc);
  vc = __riscv_vget_v_i16m2_i16m1(vp, 0);
  vd = __riscv_vget_v_i16m2_i16m1(vp, 1);

  vp = mlk_rv64v_intt2(__riscv_vle16_v_i16m2(&r[0xe0], vl2), ze);
  ve = __riscv_vget_v_i16m2_i16m1(vp, 0);
  vf = __riscv_vget_v_i16m2_i16m1(vp, 1);

  MLK_RVV_BFLY_RX(v0, v1, vt, izeta[0x40], vl);
  MLK_RVV_BFLY_RX(v2, v3, vt, izeta[0x41], vl);
  MLK_RVV_BFLY_RX(v4, v5, vt, izeta[0x50], vl);
  MLK_RVV_BFLY_RX(v6, v7, vt, izeta[0x51], vl);
  MLK_RVV_BFLY_RX(v8, v9, vt, izeta[0x60], vl);
  MLK_RVV_BFLY_RX(va, vb, vt, izeta[0x61], vl);
  MLK_RVV_BFLY_RX(vc, vd, vt, izeta[0x70], vl);
  MLK_RVV_BFLY_RX(ve, vf, vt, izeta[0x71], vl);

  MLK_RVV_BFLY_RX(v0, v2, vt, izeta[0x20], vl);
  MLK_RVV_BFLY_RX(v1, v3, vt, izeta[0x20], vl);
  MLK_RVV_BFLY_RX(v4, v6, vt, izeta[0x21], vl);
  MLK_RVV_BFLY_RX(v5, v7, vt, izeta[0x21], vl);
  MLK_RVV_BFLY_RX(v8, va, vt, izeta[0x30], vl);
  MLK_RVV_BFLY_RX(v9, vb, vt, izeta[0x30], vl);
  MLK_RVV_BFLY_RX(vc, ve, vt, izeta[0x31], vl);
  MLK_RVV_BFLY_RX(vd, vf, vt, izeta[0x31], vl);

  MLK_RVV_BFLY_RX(v0, v4, vt, izeta[0x10], vl);
  MLK_RVV_BFLY_RX(v1, v5, vt, izeta[0x10], vl);
  MLK_RVV_BFLY_RX(v2, v6, vt, izeta[0x10], vl);
  MLK_RVV_BFLY_RX(v3, v7, vt, izeta[0x10], vl);
  MLK_RVV_BFLY_RX(v8, vc, vt, izeta[0x11], vl);
  MLK_RVV_BFLY_RX(v9, vd, vt, izeta[0x11], vl);
  MLK_RVV_BFLY_RX(va, ve, vt, izeta[0x11], vl);
  MLK_RVV_BFLY_RX(vb, vf, vt, izeta[0x11], vl);

  MLK_RVV_BFLY_RX(v0, v8, vt, izeta[0x01], vl);
  MLK_RVV_BFLY_RX(v1, v9, vt, izeta[0x01], vl);
  MLK_RVV_BFLY_RX(v2, va, vt, izeta[0x01], vl);
  MLK_RVV_BFLY_RX(v3, vb, vt, izeta[0x01], vl);
  MLK_RVV_BFLY_RX(v4, vc, vt, izeta[0x01], vl);
  MLK_RVV_BFLY_RX(v5, vd, vt, izeta[0x01], vl);
  MLK_RVV_BFLY_RX(v6, ve, vt, izeta[0x01], vl);
  MLK_RVV_BFLY_RX(v7, vf, vt, izeta[0x01], vl);

  v0 = fq_mulq_vx(v0, MLK_MONT_NR, vl);
  v1 = fq_mulq_vx(v1, MLK_MONT_NR, vl);
  v2 = fq_mulq_vx(v2, MLK_MONT_NR, vl);
  v3 = fq_mulq_vx(v3, MLK_MONT_NR, vl);
  v4 = fq_mulq_vx(v4, MLK_MONT_NR, vl);
  v5 = fq_mulq_vx(v5, MLK_MONT_NR, vl);
  v6 = fq_mulq_vx(v6, MLK_MONT_NR, vl);
  v7 = fq_mulq_vx(v7, MLK_MONT_NR, vl);
  v8 = fq_mulq_vx(v8, MLK_MONT_NR, vl);
  v9 = fq_mulq_vx(v9, MLK_MONT_NR, vl);
  va = fq_mulq_vx(va, MLK_MONT_NR, vl);
  vb = fq_mulq_vx(vb, MLK_MONT_NR, vl);
  vc = fq_mulq_vx(vc, MLK_MONT_NR, vl);
  vd = fq_mulq_vx(vd, MLK_MONT_NR, vl);
  ve = fq_mulq_vx(ve, MLK_MONT_NR, vl);
  vf = fq_mulq_vx(vf, MLK_MONT_NR, vl);

  __riscv_vse16_v_i16m1(&r[0x00], v0, vl);
  __riscv_vse16_v_i16m1(&r[0x10], v1, vl);
  __riscv_vse16_v_i16m1(&r[0x20], v2, vl);
  __riscv_vse16_v_i16m1(&r[0x30], v3, vl);
  __riscv_vse16_v_i16m1(&r[0x40], v4, vl);
  __riscv_vse16_v_i16m1(&r[0x50], v5, vl);
  __riscv_vse16_v_i16m1(&r[0x60], v6, vl);
  __riscv_vse16_v_i16m1(&r[0x70], v7, vl);
  __riscv_vse16_v_i16m1(&r[0x80], v8, vl);
  __riscv_vse16_v_i16m1(&r[0x90], v9, vl);
  __riscv_vse16_v_i16m1(&r[0xa0], va, vl);
  __riscv_vse16_v_i16m1(&r[0xb0], vb, vl);
  __riscv_vse16_v_i16m1(&r[0xc0], vc, vl);
  __riscv_vse16_v_i16m1(&r[0xd0], vd, vl);
  __riscv_vse16_v_i16m1(&r[0xe0], ve, vl);
  __riscv_vse16_v_i16m1(&r[0xf0], vf, vl);
}

#undef MLK_RVV_BFLY_RX
#undef MLK_RVV_BFLY_RV

/*  Kyber's middle field GF(3329)[X]/(X^2) multiplication   */

static inline void mlk_rv64v_poly_basemul_mont_add_k(int16_t *r,
                                                     const int16_t *a,
                                                     const int16_t *b,
                                                     unsigned kn)
{
  /* check-magic: off */
  const int16_t roots[MLKEM_N] = {
      -1044, -1103, -1044, 1103,  -1044, 430,   -1044, -430,  -1044, 555,
      -1044, -555,  -1044, 843,   -1044, -843,  -1044, -1251, -1044, 1251,
      -1044, 871,   -1044, -871,  -1044, 1550,  -1044, -1550, -1044, 105,
      -1044, -105,  -1044, 422,   -1044, -422,  -1044, 587,   -1044, -587,
      -1044, 177,   -1044, -177,  -1044, -235,  -1044, 235,   -1044, -291,
      -1044, 291,   -1044, -460,  -1044, 460,   -1044, 1574,  -1044, -1574,
      -1044, 1653,  -1044, -1653, -1044, -246,  -1044, 246,   -1044, 778,
      -1044, -778,  -1044, 1159,  -1044, -1159, -1044, -147,  -1044, 147,
      -1044, -777,  -1044, 777,   -1044, 1483,  -1044, -1483, -1044, -602,
      -1044, 602,   -1044, 1119,  -1044, -1119, -1044, -1590, -1044, 1590,
      -1044, 644,   -1044, -644,  -1044, -872,  -1044, 872,   -1044, 349,
      -1044, -349,  -1044, 418,   -1044, -418,  -1044, 329,   -1044, -329,
      -1044, -156,  -1044, 156,   -1044, -75,   -1044, 75,    -1044, 817,
      -1044, -817,  -1044, 1097,  -1044, -1097, -1044, 603,   -1044, -603,
      -1044, 610,   -1044, -610,  -1044, 1322,  -1044, -1322, -1044, -1285,
      -1044, 1285,  -1044, -1465, -1044, 1465,  -1044, 384,   -1044, -384,
      -1044, -1215, -1044, 1215,  -1044, -136,  -1044, 136,   -1044, 1218,
      -1044, -1218, -1044, -1335, -1044, 1335,  -1044, -874,  -1044, 874,
      -1044, 220,   -1044, -220,  -1044, -1187, -1044, 1187,  -1044, -1659,
      -1044, 1659,  -1044, -1185, -1044, 1185,  -1044, -1530, -1044, 1530,
      -1044, -1278, -1044, 1278,  -1044, 794,   -1044, -794,  -1044, -1510,
      -1044, 1510,  -1044, -854,  -1044, 854,   -1044, -870,  -1044, 870,
      -1044, 478,   -1044, -478,  -1044, -108,  -1044, 108,   -1044, -308,
      -1044, 308,   -1044, 996,   -1044, -996,  -1044, 991,   -1044, -991,
      -1044, 958,   -1044, -958,  -1044, -1460, -1044, 1460,  -1044, 1522,
      -1044, -1522, -1044, 1628,  -1044, -1628,
  };
  /* check-magic: on */

  size_t vl = MLK_RVV_E16M1_VL;
  size_t i, j;

  const vuint16m1_t sw0 = __riscv_vxor_vx_u16m1(__riscv_vid_v_u16m1(vl), 1, vl);
  const vbool16_t sb0 = __riscv_vmseq_vx_u16m1_b16(
      __riscv_vand_vx_u16m1(__riscv_vid_v_u16m1(vl), 1, vl), 0, vl);

  vint16m1_t vt, vu;
  vint32m2_t wa, wb, ws;

  for (i = 0; i < MLKEM_N; i += vl)
  {
    const vint16m1_t vz = __riscv_vle16_v_i16m1(&roots[i], vl);

    for (j = 0; j < kn; j += MLKEM_N)
    {
      vt = __riscv_vle16_v_i16m1(&a[i + j], vl);
      vu = __riscv_vle16_v_i16m1(&b[i + j], vl);

      wa = __riscv_vwmul_vv_i32m2(vz, fq_mul_vv(vt, vu, vl), vl);
      wb = __riscv_vwmul_vv_i32m2(vt, __riscv_vrgather_vv_i16m1(vu, sw0, vl),
                                  vl);

      wa =
          __riscv_vadd_vv_i32m2(wa, __riscv_vslidedown_vx_i32m2(wa, 1, vl), vl);
      wb = __riscv_vadd_vv_i32m2(wb, __riscv_vslideup_vx_i32m2(wb, wb, 1, vl),
                                 vl);

      wa = __riscv_vmerge_vvm_i32m2(wb, wa, sb0, vl);

      if (j == 0)
      {
        ws = wa;
      }
      else
      {
        ws = __riscv_vadd_vv_i32m2(ws, wa, vl);
      }
    }
    /*  the idea is to keep 32-bit intermediate result, reduce in the end */
    __riscv_vse16_v_i16m1(&r[i], fq_redc2(ws, vl), vl);
  }
}

void mlk_rv64v_poly_basemul_mont_add_k2(int16_t *r, const int16_t *a,
                                        const int16_t *b)
{
  mlk_rv64v_poly_basemul_mont_add_k(r, a, b, 2 * MLKEM_N);
}

void mlk_rv64v_poly_basemul_mont_add_k3(int16_t *r, const int16_t *a,
                                        const int16_t *b)
{
  mlk_rv64v_poly_basemul_mont_add_k(r, a, b, 3 * MLKEM_N);
}

void mlk_rv64v_poly_basemul_mont_add_k4(int16_t *r, const int16_t *a,
                                        const int16_t *b)
{
  mlk_rv64v_poly_basemul_mont_add_k(r, a, b, 4 * MLKEM_N);
}

#endif /* MLK_RVV_VLEN == 256 */

/*************************************************
 * Name:        poly_tomont
 *
 * Description: Inplace conversion of all coefficients of a polynomial
 *              from normal domain to Montgomery domain
 *
 * Arguments:   - int16_t *r: pointer to input/output polynomial
 **************************************************/
void mlk_rv64v_poly_tomont(int16_t *r)
{
  size_t vl = MLK_RVV_E16M1_VL;

  for (size_t i = 0; i < MLKEM_N; i += vl)
  {
    __riscv_vse16_v_i16m1(
        &r[i], fq_mul_vx(__riscv_vle16_v_i16m1(&r[i], vl), MLK_MONT_R2, vl),
        vl);
  }
}

/*************************************************
 * Name:        poly_reduce
 *
 * Description: Applies Barrett reduction to all coefficients of a polynomial
 *              for details of the Barrett reduction see
 *comments in reduce.c
 *
 * Arguments:   - int16_t *r: pointer to input/output polynomial
 **************************************************/
void mlk_rv64v_poly_reduce(int16_t *r)
{
  size_t vl = MLK_RVV_E16M1_VL;
  vint16m1_t vt;

  for (size_t i = 0; i < MLKEM_N; i += vl)
  {
    vt = __riscv_vle16_v_i16m1(&r[i], vl);
    vt = fq_barrett(vt, vl);

    /*  make positive */
    vt = fq_cadd(vt, vl);
    __riscv_vse16_v_i16m1(&r[i], vt, vl);
  }
}

/*************************************************
 * Name:        poly_add
 *
 * Description: Add two polynomials; no modular reduction is performed
 *
 * Arguments: - int16_t *r: pointer to output polynomial
 *            - const int16_t *a: pointer to first input polynomial
 *            - const int16_t *b: pointer to second input polynomial
 **************************************************/
void mlk_rv64v_poly_add(int16_t *r, const int16_t *a, const int16_t *b)
{
  size_t vl = MLK_RVV_E16M1_VL;

  for (size_t i = 0; i < MLKEM_N; i += vl)
  {
    __riscv_vse16_v_i16m1(
        &r[i],
        __riscv_vadd_vv_i16m1(__riscv_vle16_v_i16m1(&a[i], vl),
                              __riscv_vle16_v_i16m1(&b[i], vl), vl),
        vl);
  }
}

/*************************************************
 * Name:        poly_sub
 *
 * Description: Subtract two polynomials; no modular reduction is performed
 *
 * Arguments: - int16_t *r:    pointer to output polynomial
 *            - const int16_t *a: pointer to first input polynomial
 *            - const int16_t *b: pointer to second input polynomial
 **************************************************/
void mlk_rv64v_poly_sub(int16_t *r, const int16_t *a, const int16_t *b)
{
  size_t vl = MLK_RVV_E16M1_VL;

  for (size_t i = 0; i < MLKEM_N; i += vl)
  {
    __riscv_vse16_v_i16m1(
        &r[i],
        __riscv_vsub_vv_i16m1(__riscv_vle16_v_i16m1(&a[i], vl),
                              __riscv_vle16_v_i16m1(&b[i], vl), vl),
        vl);
  }
}

/*  Run rejection sampling to get uniform random integers mod q  */

unsigned int mlk_rv64v_rej_uniform(int16_t *r, unsigned int len,
                                   const uint8_t *buf, unsigned int buflen)
{
  const size_t vl = MLK_RVV_E16M1_VL;
  const size_t vl23 = (MLK_RVV_E16M1_VL * 24) / 32;

  const vuint16m1_t vid = __riscv_vid_v_u16m1(vl);
  const vuint16m1_t srl12v = __riscv_vmul_vx_u16m1(vid, 12, vl);
  const vuint16m1_t sel12v = __riscv_vsrl_vx_u16m1(srl12v, 4, vl);
  const vuint16m1_t sll12v = __riscv_vsll_vx_u16m1(vid, 2, vl);

  size_t n, ctr, pos;
  vuint16m1_t x, y;
  vbool16_t lt;

  pos = 0;
  ctr = 0;

  while (ctr < len && pos + (vl23 * 2) <= buflen)
  {
    x = __riscv_vle16_v_u16m1((uint16_t *)&buf[pos], vl23);
    pos += vl23 * 2;
    x = __riscv_vrgather_vv_u16m1(x, sel12v, vl);
    x = __riscv_vor_vv_u16m1(
        __riscv_vsrl_vv_u16m1(x, srl12v, vl),
        __riscv_vsll_vv_u16m1(__riscv_vslidedown(x, 1, vl), sll12v, vl), vl);
    x = __riscv_vand_vx_u16m1(x, 0xFFF, vl);

    lt = __riscv_vmsltu_vx_u16m1_b16(x, MLKEM_Q, vl);
    y = __riscv_vcompress_vm_u16m1(x, lt, vl);
    n = __riscv_vcpop_m_b16(lt, vl);

    if (ctr + n > len)
    {
      n = len - ctr;
    }
    __riscv_vse16_v_u16m1((uint16_t *)&r[ctr], y, n);
    ctr += n;
  }

  return ctr;
}

#else /* MLK_ARITH_BACKEND_RISCV64 */

MLK_EMPTY_CU(rv64v_poly)

#endif /* !MLK_ARITH_BACKEND_RISCV64 */

/* To facilitate single-compilation-unit (SCU) builds, undefine all macros.
 * Don't modify by hand -- this is auto-generated by scripts/autogen. */
#undef MLK_RVV_BFLY_FX
#undef MLK_RVV_BFLY_FV
#undef MLK_RVV_BFLY_RX
#undef MLK_RVV_BFLY_RV
