// SPDX-License-Identifier: Apache-2.0
#include "cbd.h"
#include <stdint.h>
#include "params.h"

/*************************************************
 * Name:        load32_littleendian
 *
 * Description: load 4 bytes into a 32-bit integer
 *              in little-endian order
 *
 * Arguments:   - const uint8_t *x: pointer to input byte array
 *
 * Returns 32-bit unsigned integer loaded from x
 **************************************************/
static uint32_t load32_littleendian(const uint8_t x[4]) {
  uint32_t r;
  r = (uint32_t)x[0];
  r |= (uint32_t)x[1] << 8;
  r |= (uint32_t)x[2] << 16;
  r |= (uint32_t)x[3] << 24;
  return r;
}

/*************************************************
 * Name:        load24_littleendian
 *
 * Description: load 3 bytes into a 32-bit integer
 *              in little-endian order.
 *              This function is only needed for ML-KEM-512
 *
 * Arguments:   - const uint8_t *x: pointer to input byte array
 *
 * Returns 32-bit unsigned integer loaded from x (most significant byte is zero)
 **************************************************/
#if MLKEM_ETA1 == 3
static uint32_t load24_littleendian(const uint8_t x[3]) {
  uint32_t r;
  r = (uint32_t)x[0];
  r |= (uint32_t)x[1] << 8;
  r |= (uint32_t)x[2] << 16;
  return r;
}
#endif

/*************************************************
 * Name:        cbd2
 *
 * Description: Given an array of uniformly random bytes, compute
 *              polynomial with coefficients distributed according to
 *              a centered binomial distribution with parameter eta=2
 *
 * Arguments:   - poly *r: pointer to output polynomial
 *              - const uint8_t *buf: pointer to input byte array
 **************************************************/
static void cbd2(poly *r, const uint8_t buf[2 * MLKEM_N / 4]) {
  int i, j;
  uint32_t t, d;
  int16_t a, b;

  for (i = 0; i < MLKEM_N / 8; i++)  // clang-format off
    ASSIGNS(i, j, a, b, t, d, OBJECT_WHOLE(r))
    INVARIANT(i >= 0 && i <= MLKEM_N / 8)
    INVARIANT(ARRAY_IN_BOUNDS(0, (8 * i - 1), r->coeffs, -2, +2))  // clang-format on
    {
      t = load32_littleendian(buf + 4 * i);
      d = t & 0x55555555;
      d += (t >> 1) & 0x55555555;

      for (j = 0; j < 8; j++)  // clang-format off
        ASSIGNS(j, a, b, OBJECT_WHOLE(r))
        INVARIANT(i >= 0 && i <= MLKEM_N / 8 && j >= 0 && j <= 8)
        INVARIANT(ARRAY_IN_BOUNDS(0, 8 * i + j - 1, r->coeffs, -2, +2))  // clang-format on
        {
          a = (d >> (4 * j + 0)) & 0x3;
          b = (d >> (4 * j + 2)) & 0x3;
          r->coeffs[8 * i + j] = a - b;
        }
    }
}

/*************************************************
 * Name:        cbd3
 *
 * Description: Given an array of uniformly random bytes, compute
 *              polynomial with coefficients distributed according to
 *              a centered binomial distribution with parameter eta=3.
 *              This function is only needed for ML-KEM-512
 *
 * Arguments:   - poly *r: pointer to output polynomial
 *              - const uint8_t *buf: pointer to input byte array
 **************************************************/
#if MLKEM_ETA1 == 3
static void cbd3(poly *r, const uint8_t buf[3 * MLKEM_N / 4]) {
  int i, j;
  uint32_t t, d;
  int16_t a, b;

  for (i = 0; i < MLKEM_N / 4; i++)  // clang-format off
    ASSIGNS(i, j, a, b, t, d, OBJECT_WHOLE(r))
    INVARIANT(i >= 0 && i <= MLKEM_N / 4)
    INVARIANT(ARRAY_IN_BOUNDS(0, (4 * i - 1), r->coeffs, -3, +3))  // clang-format on
    {
      t = load24_littleendian(buf + 3 * i);
      d = t & 0x00249249;
      d += (t >> 1) & 0x00249249;
      d += (t >> 2) & 0x00249249;

      for (j = 0; j < 4; j++)  // clang-format off
        ASSIGNS(j, a, b, OBJECT_WHOLE(r))
        INVARIANT(i >= 0 && i <= MLKEM_N / 4 && j >= 0 && j <= 4)
        INVARIANT(ARRAY_IN_BOUNDS(0, 4 * i + j - 1, r->coeffs, -3, +3))  // clang-format on
        {
          a = (d >> (6 * j + 0)) & 0x7;
          b = (d >> (6 * j + 3)) & 0x7;
          r->coeffs[4 * i + j] = a - b;
        }
    }
}
#endif

void poly_cbd_eta1(poly *r, const uint8_t buf[MLKEM_ETA1 * MLKEM_N / 4]) {
#if MLKEM_ETA1 == 2
  cbd2(r, buf);
#elif MLKEM_ETA1 == 3
  cbd3(r, buf);
#else
#error "This implementation requires eta1 in {2,3}"
#endif
}

void poly_cbd_eta2(poly *r, const uint8_t buf[MLKEM_ETA2 * MLKEM_N / 4]) {
#if MLKEM_ETA2 == 2
  cbd2(r, buf);
#else
#error "This implementation requires eta2 = 2"
#endif
}