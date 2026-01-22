/*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */

/*
Implementation by the Keccak, Keyak and Ketje Teams, namely, Guido Bertoni,
Joan Daemen, Michaël Peeters, Gilles Van Assche and Ronny Van Keer, hereby
denoted as "the implementer".

For more information, feedback or questions, please refer to our websites:
http://keccak.noekeon.org/
http://keyak.noekeon.org/
http://ketje.noekeon.org/

To the extent possible under law, the implementer has waived all copyright
and related or neighboring rights to the source code in this file.
http://creativecommons.org/publicdomain/zero/1.0/
*/

/*
 * Changes for mlkem-native:
 * - MLK_COPY_FROM_STATE and MLK_COPY_TO_STATE operate on uninterleaved
 *   Keccak states in memory.
 * - Replace gather-based loading (vpgatherqq) with explicit loads and
 *   transpose operations using unpack and permute instructions.
 * - Replace individual scatter stores with batched 4-lane transpose
 *   and store operations (MLK_SCATTER_STORE256_4X).
 * - Merged prepareTheta into thetaRhoPiChiIota at the start of
 *   each round.
 * - Eliminated separate E state variables by using temporaries (Tba, etc.)
 *   and copying back to A at end of each round, removing A/E alternation.
 * - Changed ROUNDS24 from 24 unrolled macro calls to a loop-based
 *   MLK_ROUNDS_x2 processing 2 rounds per iteration.
 */


#include "../../../../common.h"
#if defined(MLK_FIPS202_X86_64_XKCP) && \
    !defined(MLK_CONFIG_MULTILEVEL_NO_SHARED)

#include <immintrin.h>
#include <stdint.h>

#include "KeccakP_1600_times4_SIMD256.h"

#ifndef MLK_SYS_LITTLE_ENDIAN
#error Expecting a little-endian platform
#endif

#define MLK_ANDNU256(a, b) _mm256_andnot_si256(a, b)
#define MLK_CONST256(a) _mm256_load_si256((const __m256i *)&(a))
#define MLK_CONST256_64(a) (__m256i) _mm256_broadcast_sd((const double *)(&a))
#define MLK_ROL64IN256(d, a, o) \
  d = _mm256_or_si256(_mm256_slli_epi64(a, o), _mm256_srli_epi64(a, 64 - (o)))
#define MLK_ROL64IN256_8(d, a) \
  d = _mm256_shuffle_epi8(a, MLK_CONST256(mlk_rho8))
#define MLK_ROL64IN256_56(d, a) \
  d = _mm256_shuffle_epi8(a, MLK_CONST256(mlk_rho56))
static const uint64_t mlk_rho8[4] = {0x0605040302010007, 0x0E0D0C0B0A09080F,
                                     0x1615141312111017, 0x1E1D1C1B1A19181F};
static const uint64_t mlk_rho56[4] = {0x0007060504030201, 0x080F0E0D0C0B0A09,
                                      0x1017161514131211, 0x181F1E1D1C1B1A19};
#define MLK_STORE256(a, b) _mm256_store_si256((__m256i *)&(a), b)
#define MLK_XOR256(a, b) _mm256_xor_si256(a, b)
#define MLK_XOREQ256(a, b) a = _mm256_xor_si256(a, b)

static MLK_ALIGN const uint64_t mlk_keccakf1600RoundConstants[24] = {
    (uint64_t)0x0000000000000001ULL, (uint64_t)0x0000000000008082ULL,
    (uint64_t)0x800000000000808aULL, (uint64_t)0x8000000080008000ULL,
    (uint64_t)0x000000000000808bULL, (uint64_t)0x0000000080000001ULL,
    (uint64_t)0x8000000080008081ULL, (uint64_t)0x8000000000008009ULL,
    (uint64_t)0x000000000000008aULL, (uint64_t)0x0000000000000088ULL,
    (uint64_t)0x0000000080008009ULL, (uint64_t)0x000000008000000aULL,
    (uint64_t)0x000000008000808bULL, (uint64_t)0x800000000000008bULL,
    (uint64_t)0x8000000000008089ULL, (uint64_t)0x8000000000008003ULL,
    (uint64_t)0x8000000000008002ULL, (uint64_t)0x8000000000000080ULL,
    (uint64_t)0x000000000000800aULL, (uint64_t)0x800000008000000aULL,
    (uint64_t)0x8000000080008081ULL, (uint64_t)0x8000000000008080ULL,
    (uint64_t)0x0000000080000001ULL, (uint64_t)0x8000000080008008ULL};

#define MLK_DECLARE_ABCDE          \
  __m256i Aba, Abe, Abi, Abo, Abu; \
  __m256i Aga, Age, Agi, Ago, Agu; \
  __m256i Aka, Ake, Aki, Ako, Aku; \
  __m256i Ama, Ame, Ami, Amo, Amu; \
  __m256i Asa, Ase, Asi, Aso, Asu; \
  __m256i Bba, Bbe, Bbi, Bbo, Bbu; \
  __m256i Bga, Bge, Bgi, Bgo, Bgu; \
  __m256i Bka, Bke, Bki, Bko, Bku; \
  __m256i Bma, Bme, Bmi, Bmo, Bmu; \
  __m256i Bsa, Bse, Bsi, Bso, Bsu; \
  __m256i Ca, Ce, Ci, Co, Cu;      \
  __m256i Ca1, Ce1, Ci1, Co1, Cu1; \
  __m256i Da, De, Di, Do, Du;      \
  __m256i Tba, Tbe, Tbi, Tbo, Tbu; \
  __m256i Tga, Tge, Tgi, Tgo, Tgu; \
  __m256i Tka, Tke, Tki, Tko, Tku; \
  __m256i Tma, Tme, Tmi, Tmo, Tmu; \
  __m256i Tsa, Tse, Tsi, Tso, Tsu;

/*
 * --- Theta Rho Pi Chi Iota
 * --- 64-bit lanes mapped to 64-bit words
 */
#define MLK_thetaRhoPiChiIota(i, A)                                           \
  Ca = MLK_XOR256(                                                            \
      A##ba, MLK_XOR256(A##ga, MLK_XOR256(A##ka, MLK_XOR256(A##ma, A##sa)))); \
  Ce = MLK_XOR256(                                                            \
      A##be, MLK_XOR256(A##ge, MLK_XOR256(A##ke, MLK_XOR256(A##me, A##se)))); \
  Ci = MLK_XOR256(                                                            \
      A##bi, MLK_XOR256(A##gi, MLK_XOR256(A##ki, MLK_XOR256(A##mi, A##si)))); \
  Co = MLK_XOR256(                                                            \
      A##bo, MLK_XOR256(A##go, MLK_XOR256(A##ko, MLK_XOR256(A##mo, A##so)))); \
  Cu = MLK_XOR256(                                                            \
      A##bu, MLK_XOR256(A##gu, MLK_XOR256(A##ku, MLK_XOR256(A##mu, A##su)))); \
                                                                              \
  MLK_ROL64IN256(Ce1, Ce, 1);                                                 \
  Da = MLK_XOR256(Cu, Ce1);                                                   \
  MLK_ROL64IN256(Ci1, Ci, 1);                                                 \
  De = MLK_XOR256(Ca, Ci1);                                                   \
  MLK_ROL64IN256(Co1, Co, 1);                                                 \
  Di = MLK_XOR256(Ce, Co1);                                                   \
  MLK_ROL64IN256(Cu1, Cu, 1);                                                 \
  Do = MLK_XOR256(Ci, Cu1);                                                   \
  MLK_ROL64IN256(Ca1, Ca, 1);                                                 \
  Du = MLK_XOR256(Co, Ca1);                                                   \
                                                                              \
  MLK_XOREQ256(A##ba, Da);                                                    \
  Bba = A##ba;                                                                \
  MLK_XOREQ256(A##ge, De);                                                    \
  MLK_ROL64IN256(Bbe, A##ge, 44);                                             \
  MLK_XOREQ256(A##ki, Di);                                                    \
  MLK_ROL64IN256(Bbi, A##ki, 43);                                             \
  Tba = MLK_XOR256(Bba, MLK_ANDNU256(Bbe, Bbi));                              \
  MLK_XOREQ256(Tba, MLK_CONST256_64(mlk_keccakf1600RoundConstants[i]));       \
  Ca = Tba;                                                                   \
  MLK_XOREQ256(A##mo, Do);                                                    \
  MLK_ROL64IN256(Bbo, A##mo, 21);                                             \
  Tbe = MLK_XOR256(Bbe, MLK_ANDNU256(Bbi, Bbo));                              \
  Ce = Tbe;                                                                   \
  MLK_XOREQ256(A##su, Du);                                                    \
  MLK_ROL64IN256(Bbu, A##su, 14);                                             \
  Tbi = MLK_XOR256(Bbi, MLK_ANDNU256(Bbo, Bbu));                              \
  Ci = Tbi;                                                                   \
  Tbo = MLK_XOR256(Bbo, MLK_ANDNU256(Bbu, Bba));                              \
  Co = Tbo;                                                                   \
  Tbu = MLK_XOR256(Bbu, MLK_ANDNU256(Bba, Bbe));                              \
  Cu = Tbu;                                                                   \
                                                                              \
  MLK_XOREQ256(A##bo, Do);                                                    \
  MLK_ROL64IN256(Bga, A##bo, 28);                                             \
  MLK_XOREQ256(A##gu, Du);                                                    \
  MLK_ROL64IN256(Bge, A##gu, 20);                                             \
  MLK_XOREQ256(A##ka, Da);                                                    \
  MLK_ROL64IN256(Bgi, A##ka, 3);                                              \
  Tga = MLK_XOR256(Bga, MLK_ANDNU256(Bge, Bgi));                              \
  MLK_XOREQ256(Ca, Tga);                                                      \
  MLK_XOREQ256(A##me, De);                                                    \
  MLK_ROL64IN256(Bgo, A##me, 45);                                             \
  Tge = MLK_XOR256(Bge, MLK_ANDNU256(Bgi, Bgo));                              \
  MLK_XOREQ256(Ce, Tge);                                                      \
  MLK_XOREQ256(A##si, Di);                                                    \
  MLK_ROL64IN256(Bgu, A##si, 61);                                             \
  Tgi = MLK_XOR256(Bgi, MLK_ANDNU256(Bgo, Bgu));                              \
  MLK_XOREQ256(Ci, Tgi);                                                      \
  Tgo = MLK_XOR256(Bgo, MLK_ANDNU256(Bgu, Bga));                              \
  MLK_XOREQ256(Co, Tgo);                                                      \
  Tgu = MLK_XOR256(Bgu, MLK_ANDNU256(Bga, Bge));                              \
  MLK_XOREQ256(Cu, Tgu);                                                      \
                                                                              \
  MLK_XOREQ256(A##be, De);                                                    \
  MLK_ROL64IN256(Bka, A##be, 1);                                              \
  MLK_XOREQ256(A##gi, Di);                                                    \
  MLK_ROL64IN256(Bke, A##gi, 6);                                              \
  MLK_XOREQ256(A##ko, Do);                                                    \
  MLK_ROL64IN256(Bki, A##ko, 25);                                             \
  Tka = MLK_XOR256(Bka, MLK_ANDNU256(Bke, Bki));                              \
  MLK_XOREQ256(Ca, Tka);                                                      \
  MLK_XOREQ256(A##mu, Du);                                                    \
  MLK_ROL64IN256_8(Bko, A##mu);                                               \
  Tke = MLK_XOR256(Bke, MLK_ANDNU256(Bki, Bko));                              \
  MLK_XOREQ256(Ce, Tke);                                                      \
  MLK_XOREQ256(A##sa, Da);                                                    \
  MLK_ROL64IN256(Bku, A##sa, 18);                                             \
  Tki = MLK_XOR256(Bki, MLK_ANDNU256(Bko, Bku));                              \
  MLK_XOREQ256(Ci, Tki);                                                      \
  Tko = MLK_XOR256(Bko, MLK_ANDNU256(Bku, Bka));                              \
  MLK_XOREQ256(Co, Tko);                                                      \
  Tku = MLK_XOR256(Bku, MLK_ANDNU256(Bka, Bke));                              \
  MLK_XOREQ256(Cu, Tku);                                                      \
                                                                              \
  MLK_XOREQ256(A##bu, Du);                                                    \
  MLK_ROL64IN256(Bma, A##bu, 27);                                             \
  MLK_XOREQ256(A##ga, Da);                                                    \
  MLK_ROL64IN256(Bme, A##ga, 36);                                             \
  MLK_XOREQ256(A##ke, De);                                                    \
  MLK_ROL64IN256(Bmi, A##ke, 10);                                             \
  Tma = MLK_XOR256(Bma, MLK_ANDNU256(Bme, Bmi));                              \
  MLK_XOREQ256(Ca, Tma);                                                      \
  MLK_XOREQ256(A##mi, Di);                                                    \
  MLK_ROL64IN256(Bmo, A##mi, 15);                                             \
  Tme = MLK_XOR256(Bme, MLK_ANDNU256(Bmi, Bmo));                              \
  MLK_XOREQ256(Ce, Tme);                                                      \
  MLK_XOREQ256(A##so, Do);                                                    \
  MLK_ROL64IN256_56(Bmu, A##so);                                              \
  Tmi = MLK_XOR256(Bmi, MLK_ANDNU256(Bmo, Bmu));                              \
  MLK_XOREQ256(Ci, Tmi);                                                      \
  Tmo = MLK_XOR256(Bmo, MLK_ANDNU256(Bmu, Bma));                              \
  MLK_XOREQ256(Co, Tmo);                                                      \
  Tmu = MLK_XOR256(Bmu, MLK_ANDNU256(Bma, Bme));                              \
  MLK_XOREQ256(Cu, Tmu);                                                      \
                                                                              \
  MLK_XOREQ256(A##bi, Di);                                                    \
  MLK_ROL64IN256(Bsa, A##bi, 62);                                             \
  MLK_XOREQ256(A##go, Do);                                                    \
  MLK_ROL64IN256(Bse, A##go, 55);                                             \
  MLK_XOREQ256(A##ku, Du);                                                    \
  MLK_ROL64IN256(Bsi, A##ku, 39);                                             \
  Tsa = MLK_XOR256(Bsa, MLK_ANDNU256(Bse, Bsi));                              \
  MLK_XOREQ256(Ca, Tsa);                                                      \
  MLK_XOREQ256(A##ma, Da);                                                    \
  MLK_ROL64IN256(Bso, A##ma, 41);                                             \
  Tse = MLK_XOR256(Bse, MLK_ANDNU256(Bsi, Bso));                              \
  MLK_XOREQ256(Ce, Tse);                                                      \
  MLK_XOREQ256(A##se, De);                                                    \
  MLK_ROL64IN256(Bsu, A##se, 2);                                              \
  Tsi = MLK_XOR256(Bsi, MLK_ANDNU256(Bso, Bsu));                              \
  MLK_XOREQ256(Ci, Tsi);                                                      \
  Tso = MLK_XOR256(Bso, MLK_ANDNU256(Bsu, Bsa));                              \
  MLK_XOREQ256(Co, Tso);                                                      \
  Tsu = MLK_XOR256(Bsu, MLK_ANDNU256(Bsa, Bse));                              \
  MLK_XOREQ256(Cu, Tsu);                                                      \
                                                                              \
  A##ba = Tba;                                                                \
  A##be = Tbe;                                                                \
  A##bi = Tbi;                                                                \
  A##bo = Tbo;                                                                \
  A##bu = Tbu;                                                                \
  A##ga = Tga;                                                                \
  A##ge = Tge;                                                                \
  A##gi = Tgi;                                                                \
  A##go = Tgo;                                                                \
  A##gu = Tgu;                                                                \
  A##ka = Tka;                                                                \
  A##ke = Tke;                                                                \
  A##ki = Tki;                                                                \
  A##ko = Tko;                                                                \
  A##ku = Tku;                                                                \
  A##ma = Tma;                                                                \
  A##me = Tme;                                                                \
  A##mi = Tmi;                                                                \
  A##mo = Tmo;                                                                \
  A##mu = Tmu;                                                                \
  A##sa = Tsa;                                                                \
  A##se = Tse;                                                                \
  A##si = Tsi;                                                                \
  A##so = Tso;                                                                \
  A##su = Tsu;

#define MLK_LOAD_LANE_4X(X0, X1, X2, X3, state, lane)                \
  do                                                                 \
  {                                                                  \
    const uint64_t *state64 = (const uint64_t *)(state);             \
    __m256i t0, t1, t2, t3;                                          \
    __m256i tmp0, tmp1, tmp2, tmp3;                                  \
    tmp0 = _mm256_loadu_si256((const __m256i *)&state64[lane]);      \
    tmp1 = _mm256_loadu_si256((const __m256i *)&state64[lane + 25]); \
    tmp2 = _mm256_loadu_si256((const __m256i *)&state64[lane + 50]); \
    tmp3 = _mm256_loadu_si256((const __m256i *)&state64[lane + 75]); \
                                                                     \
    t0 = _mm256_unpacklo_epi64(tmp0, tmp1);                          \
    t1 = _mm256_unpackhi_epi64(tmp0, tmp1);                          \
    t2 = _mm256_unpacklo_epi64(tmp2, tmp3);                          \
    t3 = _mm256_unpackhi_epi64(tmp2, tmp3);                          \
                                                                     \
    X0 = _mm256_permute2x128_si256(t0, t2, 0x20);                    \
    X1 = _mm256_permute2x128_si256(t1, t3, 0x20);                    \
    X2 = _mm256_permute2x128_si256(t0, t2, 0x31);                    \
    X3 = _mm256_permute2x128_si256(t1, t3, 0x31);                    \
  } while (0)

#define MLK_LOAD_LANE_1X(X, state, lane)                              \
  do                                                                  \
  {                                                                   \
    const uint64_t *state64 = (const uint64_t *)(state);              \
    X = _mm256_set_epi64x(                                            \
        (long long)state64[lane + 75], (long long)state64[lane + 50], \
        (long long)state64[lane + 25], (long long)state64[lane]);     \
  } while (0)

#define MLK_COPY_FROM_STATE(X, state)                        \
  do                                                         \
  {                                                          \
    MLK_LOAD_LANE_4X(X##ba, X##be, X##bi, X##bo, state, 0);  \
    MLK_LOAD_LANE_4X(X##bu, X##ga, X##ge, X##gi, state, 4);  \
    MLK_LOAD_LANE_4X(X##go, X##gu, X##ka, X##ke, state, 8);  \
    MLK_LOAD_LANE_4X(X##ki, X##ko, X##ku, X##ma, state, 12); \
    MLK_LOAD_LANE_4X(X##me, X##mi, X##mo, X##mu, state, 16); \
    MLK_LOAD_LANE_4X(X##sa, X##se, X##si, X##so, state, 20); \
    MLK_LOAD_LANE_1X(X##su, state, 24);                      \
  } while (0)

#define MLK_SCATTER_STORE256_4X(state, idx, lane0, lane1, lane2, lane3) \
  do                                                                    \
  {                                                                     \
    uint64_t *state64 = (uint64_t *)(state);                            \
    __m256i t0, t1, t2, t3;                                             \
    __m256i tmp0, tmp1, tmp2, tmp3;                                     \
    tmp0 = _mm256_unpacklo_epi64(lane0, lane1);                         \
    tmp1 = _mm256_unpackhi_epi64(lane0, lane1);                         \
    tmp2 = _mm256_unpacklo_epi64(lane2, lane3);                         \
    tmp3 = _mm256_unpackhi_epi64(lane2, lane3);                         \
                                                                        \
    t0 = _mm256_permute2x128_si256(tmp0, tmp2, 0x20);                   \
    t1 = _mm256_permute2x128_si256(tmp1, tmp3, 0x20);                   \
    t2 = _mm256_permute2x128_si256(tmp0, tmp2, 0x31);                   \
    t3 = _mm256_permute2x128_si256(tmp1, tmp3, 0x31);                   \
                                                                        \
    _mm256_storeu_si256((__m256i *)&state64[(idx)], t0);                \
    _mm256_storeu_si256((__m256i *)&state64[(idx) + 25], t1);           \
    _mm256_storeu_si256((__m256i *)&state64[(idx) + 50], t2);           \
    _mm256_storeu_si256((__m256i *)&state64[(idx) + 75], t3);           \
  } while (0)

#define MLK_SCATTER_STORE256_1X(state, idx, v)                 \
  do                                                           \
  {                                                            \
    const uint64_t *state64 = (const uint64_t *)(state);       \
    __m128d t = _mm_castsi128_pd(_mm256_castsi256_si128((v))); \
    _mm_storel_pd((double *)&state64[0 + (idx)], t);           \
    _mm_storeh_pd((double *)&state64[25 + (idx)], t);          \
    t = _mm_castsi128_pd(_mm256_extracti128_si256((v), 1));    \
    _mm_storel_pd((double *)&state64[50 + (idx)], t);          \
    _mm_storeh_pd((double *)&state64[75 + (idx)], t);          \
  } while (0)

#define MLK_COPY_TO_STATE(state, X)                                 \
  do                                                                \
  {                                                                 \
    MLK_SCATTER_STORE256_4X(state, 0, X##ba, X##be, X##bi, X##bo);  \
    MLK_SCATTER_STORE256_4X(state, 4, X##bu, X##ga, X##ge, X##gi);  \
    MLK_SCATTER_STORE256_4X(state, 8, X##go, X##gu, X##ka, X##ke);  \
    MLK_SCATTER_STORE256_4X(state, 12, X##ki, X##ko, X##ku, X##ma); \
    MLK_SCATTER_STORE256_4X(state, 16, X##me, X##mi, X##mo, X##mu); \
    MLK_SCATTER_STORE256_4X(state, 20, X##sa, X##se, X##si, X##so); \
    MLK_SCATTER_STORE256_1X(state, 24, X##su);                      \
  } while (0)

/* clang-format off */
#define MLK_ROUNDS_x2                                               \
      do {                                                          \
        int i;                                                      \
        for (i = 0; i < 12; i++) {                                  \
            MLK_thetaRhoPiChiIota( 2*i, A)                          \
            MLK_thetaRhoPiChiIota( 2*i+1, A)                        \
        }                                                           \
    } while(0)
/* clang-format on */

void mlk_keccakf1600x4_permute24(void *states)
{
  __m256i *statesAsLanes = (__m256i *)states;
  MLK_DECLARE_ABCDE;
  MLK_COPY_FROM_STATE(A, statesAsLanes);
  MLK_ROUNDS_x2;
  MLK_COPY_TO_STATE(statesAsLanes, A);
}

#else /* MLK_FIPS202_X86_64_XKCP && !MLK_CONFIG_MULTILEVEL_NO_SHARED */

MLK_EMPTY_CU(fips202_avx2_keccakx4)

#endif /* !(MLK_FIPS202_X86_64_XKCP && !MLK_CONFIG_MULTILEVEL_NO_SHARED) */

/* To facilitate single-compilation-unit (SCU) builds, undefine all macros.
 * Don't modify by hand -- this is auto-generated by scripts/autogen. */
#undef MLK_ANDNU256
#undef MLK_CONST256
#undef MLK_CONST256_64
#undef MLK_ROL64IN256
#undef MLK_ROL64IN256_8
#undef MLK_ROL64IN256_56
#undef MLK_STORE256
#undef MLK_XOR256
#undef MLK_XOREQ256
#undef MLK_DECLARE_ABCDE
#undef MLK_thetaRhoPiChiIota
#undef MLK_LOAD_LANE_4X
#undef MLK_LOAD_LANE_1X
#undef MLK_COPY_FROM_STATE
#undef MLK_SCATTER_STORE256_4X
#undef MLK_SCATTER_STORE256_1X
#undef MLK_COPY_TO_STATE
#undef MLK_ROUNDS_x2
