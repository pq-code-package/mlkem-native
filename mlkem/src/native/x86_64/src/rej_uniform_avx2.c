/*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */

/* References
 * ==========
 *
 * - [REF_AVX2]
 *   CRYSTALS-Kyber optimized AVX2 implementation
 *   Bos, Ducas, Kiltz, Lepoint, Lyubashevsky, Schanck, Schwabe, Seiler, Stehlé
 *   https://github.com/pq-crystals/kyber/tree/main/avx2
 */

/*
 * This file is derived from the public domain
 * AVX2 Kyber implementation @[REF_AVX2].
 */

#include "../../../common.h"

#if defined(MLK_ARITH_BACKEND_X86_64_DEFAULT) && \
    !defined(MLK_CONFIG_MULTILEVEL_NO_SHARED)

#include <immintrin.h>
#include <stdint.h>
#include <string.h>
#include "arith_native_x86_64.h"
#include "consts.h"

unsigned mlk_rej_uniform_avx2(int16_t *MLK_RESTRICT r, const uint8_t *buf)
{
  unsigned ctr, pos;
  uint16_t val0, val1;
  uint32_t good;
  const __m128i bound = _mm_set1_epi16(MLKEM_Q);
  const __m128i mask = _mm_set1_epi16(0xFFF);
  const __m128i idx8 =
      _mm_set_epi8(11, 10, 10, 9, 8, 7, 7, 6, 5, 4, 4, 3, 2, 1, 1, 0);
  __m128i f, t, pilo;

  ctr = pos = 0;
  while (ctr <= MLKEM_N - 8 && pos <= MLK_AVX2_REJ_UNIFORM_BUFLEN - 12)
  {
    f = _mm_loadu_si128((__m128i *)&buf[pos]);
    f = _mm_shuffle_epi8(f, idx8);
    t = _mm_srli_epi16(f, 4);
    f = _mm_blend_epi16(f, t, 0xAA);
    f = _mm_and_si128(f, mask);
    pos += 12;

    t = _mm_cmpgt_epi16(bound, f);
    good = _mm_movemask_epi8(t);

    good = _pext_u32(good, 0x5555);
    pilo = _mm_loadu_si128((__m128i *)&mlk_rej_uniform_table[16 * good]);

    f = _mm_shuffle_epi8(f, pilo);
    _mm_storeu_si128((__m128i *)&r[ctr], f);
    ctr += _mm_popcnt_u32(good);
  }

  while (ctr < MLKEM_N && pos <= MLK_AVX2_REJ_UNIFORM_BUFLEN - 3)
  {
    val0 = ((buf[pos + 0] >> 0) | ((uint16_t)buf[pos + 1] << 8)) & 0xFFF;
    val1 = ((buf[pos + 1] >> 4) | ((uint16_t)buf[pos + 2] << 4));
    pos += 3;

    if (val0 < MLKEM_Q)
    {
      r[ctr++] = val0;
    }
    if (val1 < MLKEM_Q && ctr < MLKEM_N)
    {
      r[ctr++] = val1;
    }
  }

  return ctr;
}

#else /* MLK_ARITH_BACKEND_X86_64_DEFAULT && !MLK_CONFIG_MULTILEVEL_NO_SHARED \
       */

MLK_EMPTY_CU(avx2_rej_uniform)

#endif /* !(MLK_ARITH_BACKEND_X86_64_DEFAULT && \
          !MLK_CONFIG_MULTILEVEL_NO_SHARED) */
