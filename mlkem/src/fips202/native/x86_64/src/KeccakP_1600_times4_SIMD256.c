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
#define MLK_ROL64IN256_8(d, a) d = _mm256_shuffle_epi8(a, MLK_CONST256(rho8))
#define MLK_ROL64IN256_56(d, a) d = _mm256_shuffle_epi8(a, MLK_CONST256(rho56))
static const uint64_t rho8[4] = {0x0605040302010007, 0x0E0D0C0B0A09080F,
                                 0x1615141312111017, 0x1E1D1C1B1A19181F};
static const uint64_t rho56[4] = {0x0007060504030201, 0x080F0E0D0C0B0A09,
                                  0x1017161514131211, 0x181F1E1D1C1B1A19};
#define MLK_STORE256(a, b) _mm256_store_si256((__m256i *)&(a), b)
#define MLK_XOR256(a, b) _mm256_xor_si256(a, b)
#define MLK_XOREQ256(a, b) a = _mm256_xor_si256(a, b)

#define MLK_SNP_LANELENGTHINBYTES 8

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
  __m256i Eba, Ebe, Ebi, Ebo, Ebu; \
  __m256i Ega, Ege, Egi, Ego, Egu; \
  __m256i Eka, Eke, Eki, Eko, Eku; \
  __m256i Ema, Eme, Emi, Emo, Emu; \
  __m256i Esa, Ese, Esi, Eso, Esu;

#define MLK_prepareTheta                                                       \
  Ca =                                                                         \
      MLK_XOR256(Aba, MLK_XOR256(Aga, MLK_XOR256(Aka, MLK_XOR256(Ama, Asa)))); \
  Ce =                                                                         \
      MLK_XOR256(Abe, MLK_XOR256(Age, MLK_XOR256(Ake, MLK_XOR256(Ame, Ase)))); \
  Ci =                                                                         \
      MLK_XOR256(Abi, MLK_XOR256(Agi, MLK_XOR256(Aki, MLK_XOR256(Ami, Asi)))); \
  Co =                                                                         \
      MLK_XOR256(Abo, MLK_XOR256(Ago, MLK_XOR256(Ako, MLK_XOR256(Amo, Aso)))); \
  Cu = MLK_XOR256(Abu, MLK_XOR256(Agu, MLK_XOR256(Aku, MLK_XOR256(Amu, Asu))));

/*
 * --- Theta Rho Pi Chi Iota Prepare-theta
 * --- 64-bit lanes mapped to 64-bit words
 */
#define MLK_thetaRhoPiChiIotaPrepareTheta(i, A, E)                    \
  MLK_ROL64IN256(Ce1, Ce, 1);                                         \
  Da = MLK_XOR256(Cu, Ce1);                                           \
  MLK_ROL64IN256(Ci1, Ci, 1);                                         \
  De = MLK_XOR256(Ca, Ci1);                                           \
  MLK_ROL64IN256(Co1, Co, 1);                                         \
  Di = MLK_XOR256(Ce, Co1);                                           \
  MLK_ROL64IN256(Cu1, Cu, 1);                                         \
  Do = MLK_XOR256(Ci, Cu1);                                           \
  MLK_ROL64IN256(Ca1, Ca, 1);                                         \
  Du = MLK_XOR256(Co, Ca1);                                           \
                                                                      \
  MLK_XOREQ256(A##ba, Da);                                            \
  Bba = A##ba;                                                        \
  MLK_XOREQ256(A##ge, De);                                            \
  MLK_ROL64IN256(Bbe, A##ge, 44);                                     \
  MLK_XOREQ256(A##ki, Di);                                            \
  MLK_ROL64IN256(Bbi, A##ki, 43);                                     \
  E##ba = MLK_XOR256(Bba, MLK_ANDNU256(Bbe, Bbi));                    \
  MLK_XOREQ256(E##ba, MLK_CONST256_64(keccakf1600RoundConstants[i])); \
  Ca = E##ba;                                                         \
  MLK_XOREQ256(A##mo, Do);                                            \
  MLK_ROL64IN256(Bbo, A##mo, 21);                                     \
  E##be = MLK_XOR256(Bbe, MLK_ANDNU256(Bbi, Bbo));                    \
  Ce = E##be;                                                         \
  MLK_XOREQ256(A##su, Du);                                            \
  MLK_ROL64IN256(Bbu, A##su, 14);                                     \
  E##bi = MLK_XOR256(Bbi, MLK_ANDNU256(Bbo, Bbu));                    \
  Ci = E##bi;                                                         \
  E##bo = MLK_XOR256(Bbo, MLK_ANDNU256(Bbu, Bba));                    \
  Co = E##bo;                                                         \
  E##bu = MLK_XOR256(Bbu, MLK_ANDNU256(Bba, Bbe));                    \
  Cu = E##bu;                                                         \
                                                                      \
  MLK_XOREQ256(A##bo, Do);                                            \
  MLK_ROL64IN256(Bga, A##bo, 28);                                     \
  MLK_XOREQ256(A##gu, Du);                                            \
  MLK_ROL64IN256(Bge, A##gu, 20);                                     \
  MLK_XOREQ256(A##ka, Da);                                            \
  MLK_ROL64IN256(Bgi, A##ka, 3);                                      \
  E##ga = MLK_XOR256(Bga, MLK_ANDNU256(Bge, Bgi));                    \
  MLK_XOREQ256(Ca, E##ga);                                            \
  MLK_XOREQ256(A##me, De);                                            \
  MLK_ROL64IN256(Bgo, A##me, 45);                                     \
  E##ge = MLK_XOR256(Bge, MLK_ANDNU256(Bgi, Bgo));                    \
  MLK_XOREQ256(Ce, E##ge);                                            \
  MLK_XOREQ256(A##si, Di);                                            \
  MLK_ROL64IN256(Bgu, A##si, 61);                                     \
  E##gi = MLK_XOR256(Bgi, MLK_ANDNU256(Bgo, Bgu));                    \
  MLK_XOREQ256(Ci, E##gi);                                            \
  E##go = MLK_XOR256(Bgo, MLK_ANDNU256(Bgu, Bga));                    \
  MLK_XOREQ256(Co, E##go);                                            \
  E##gu = MLK_XOR256(Bgu, MLK_ANDNU256(Bga, Bge));                    \
  MLK_XOREQ256(Cu, E##gu);                                            \
                                                                      \
  MLK_XOREQ256(A##be, De);                                            \
  MLK_ROL64IN256(Bka, A##be, 1);                                      \
  MLK_XOREQ256(A##gi, Di);                                            \
  MLK_ROL64IN256(Bke, A##gi, 6);                                      \
  MLK_XOREQ256(A##ko, Do);                                            \
  MLK_ROL64IN256(Bki, A##ko, 25);                                     \
  E##ka = MLK_XOR256(Bka, MLK_ANDNU256(Bke, Bki));                    \
  MLK_XOREQ256(Ca, E##ka);                                            \
  MLK_XOREQ256(A##mu, Du);                                            \
  MLK_ROL64IN256_8(Bko, A##mu);                                       \
  E##ke = MLK_XOR256(Bke, MLK_ANDNU256(Bki, Bko));                    \
  MLK_XOREQ256(Ce, E##ke);                                            \
  MLK_XOREQ256(A##sa, Da);                                            \
  MLK_ROL64IN256(Bku, A##sa, 18);                                     \
  E##ki = MLK_XOR256(Bki, MLK_ANDNU256(Bko, Bku));                    \
  MLK_XOREQ256(Ci, E##ki);                                            \
  E##ko = MLK_XOR256(Bko, MLK_ANDNU256(Bku, Bka));                    \
  MLK_XOREQ256(Co, E##ko);                                            \
  E##ku = MLK_XOR256(Bku, MLK_ANDNU256(Bka, Bke));                    \
  MLK_XOREQ256(Cu, E##ku);                                            \
                                                                      \
  MLK_XOREQ256(A##bu, Du);                                            \
  MLK_ROL64IN256(Bma, A##bu, 27);                                     \
  MLK_XOREQ256(A##ga, Da);                                            \
  MLK_ROL64IN256(Bme, A##ga, 36);                                     \
  MLK_XOREQ256(A##ke, De);                                            \
  MLK_ROL64IN256(Bmi, A##ke, 10);                                     \
  E##ma = MLK_XOR256(Bma, MLK_ANDNU256(Bme, Bmi));                    \
  MLK_XOREQ256(Ca, E##ma);                                            \
  MLK_XOREQ256(A##mi, Di);                                            \
  MLK_ROL64IN256(Bmo, A##mi, 15);                                     \
  E##me = MLK_XOR256(Bme, MLK_ANDNU256(Bmi, Bmo));                    \
  MLK_XOREQ256(Ce, E##me);                                            \
  MLK_XOREQ256(A##so, Do);                                            \
  MLK_ROL64IN256_56(Bmu, A##so);                                      \
  E##mi = MLK_XOR256(Bmi, MLK_ANDNU256(Bmo, Bmu));                    \
  MLK_XOREQ256(Ci, E##mi);                                            \
  E##mo = MLK_XOR256(Bmo, MLK_ANDNU256(Bmu, Bma));                    \
  MLK_XOREQ256(Co, E##mo);                                            \
  E##mu = MLK_XOR256(Bmu, MLK_ANDNU256(Bma, Bme));                    \
  MLK_XOREQ256(Cu, E##mu);                                            \
                                                                      \
  MLK_XOREQ256(A##bi, Di);                                            \
  MLK_ROL64IN256(Bsa, A##bi, 62);                                     \
  MLK_XOREQ256(A##go, Do);                                            \
  MLK_ROL64IN256(Bse, A##go, 55);                                     \
  MLK_XOREQ256(A##ku, Du);                                            \
  MLK_ROL64IN256(Bsi, A##ku, 39);                                     \
  E##sa = MLK_XOR256(Bsa, MLK_ANDNU256(Bse, Bsi));                    \
  MLK_XOREQ256(Ca, E##sa);                                            \
  MLK_XOREQ256(A##ma, Da);                                            \
  MLK_ROL64IN256(Bso, A##ma, 41);                                     \
  E##se = MLK_XOR256(Bse, MLK_ANDNU256(Bsi, Bso));                    \
  MLK_XOREQ256(Ce, E##se);                                            \
  MLK_XOREQ256(A##se, De);                                            \
  MLK_ROL64IN256(Bsu, A##se, 2);                                      \
  E##si = MLK_XOR256(Bsi, MLK_ANDNU256(Bso, Bsu));                    \
  MLK_XOREQ256(Ci, E##si);                                            \
  E##so = MLK_XOR256(Bso, MLK_ANDNU256(Bsu, Bsa));                    \
  MLK_XOREQ256(Co, E##so);                                            \
  E##su = MLK_XOR256(Bsu, MLK_ANDNU256(Bsa, Bse));                    \
  MLK_XOREQ256(Cu, E##su);


/*
 * --- Theta Rho Pi Chi Iota
 * --- 64-bit lanes mapped to 64-bit words
 */
#define MLK_thetaRhoPiChiIota(i, A, E)                                \
  MLK_ROL64IN256(Ce1, Ce, 1);                                         \
  Da = MLK_XOR256(Cu, Ce1);                                           \
  MLK_ROL64IN256(Ci1, Ci, 1);                                         \
  De = MLK_XOR256(Ca, Ci1);                                           \
  MLK_ROL64IN256(Co1, Co, 1);                                         \
  Di = MLK_XOR256(Ce, Co1);                                           \
  MLK_ROL64IN256(Cu1, Cu, 1);                                         \
  Do = MLK_XOR256(Ci, Cu1);                                           \
  MLK_ROL64IN256(Ca1, Ca, 1);                                         \
  Du = MLK_XOR256(Co, Ca1);                                           \
                                                                      \
  MLK_XOREQ256(A##ba, Da);                                            \
  Bba = A##ba;                                                        \
  MLK_XOREQ256(A##ge, De);                                            \
  MLK_ROL64IN256(Bbe, A##ge, 44);                                     \
  MLK_XOREQ256(A##ki, Di);                                            \
  MLK_ROL64IN256(Bbi, A##ki, 43);                                     \
  E##ba = MLK_XOR256(Bba, MLK_ANDNU256(Bbe, Bbi));                    \
  MLK_XOREQ256(E##ba, MLK_CONST256_64(keccakf1600RoundConstants[i])); \
  MLK_XOREQ256(A##mo, Do);                                            \
  MLK_ROL64IN256(Bbo, A##mo, 21);                                     \
  E##be = MLK_XOR256(Bbe, MLK_ANDNU256(Bbi, Bbo));                    \
  MLK_XOREQ256(A##su, Du);                                            \
  MLK_ROL64IN256(Bbu, A##su, 14);                                     \
  E##bi = MLK_XOR256(Bbi, MLK_ANDNU256(Bbo, Bbu));                    \
  E##bo = MLK_XOR256(Bbo, MLK_ANDNU256(Bbu, Bba));                    \
  E##bu = MLK_XOR256(Bbu, MLK_ANDNU256(Bba, Bbe));                    \
                                                                      \
  MLK_XOREQ256(A##bo, Do);                                            \
  MLK_ROL64IN256(Bga, A##bo, 28);                                     \
  MLK_XOREQ256(A##gu, Du);                                            \
  MLK_ROL64IN256(Bge, A##gu, 20);                                     \
  MLK_XOREQ256(A##ka, Da);                                            \
  MLK_ROL64IN256(Bgi, A##ka, 3);                                      \
  E##ga = MLK_XOR256(Bga, MLK_ANDNU256(Bge, Bgi));                    \
  MLK_XOREQ256(A##me, De);                                            \
  MLK_ROL64IN256(Bgo, A##me, 45);                                     \
  E##ge = MLK_XOR256(Bge, MLK_ANDNU256(Bgi, Bgo));                    \
  MLK_XOREQ256(A##si, Di);                                            \
  MLK_ROL64IN256(Bgu, A##si, 61);                                     \
  E##gi = MLK_XOR256(Bgi, MLK_ANDNU256(Bgo, Bgu));                    \
  E##go = MLK_XOR256(Bgo, MLK_ANDNU256(Bgu, Bga));                    \
  E##gu = MLK_XOR256(Bgu, MLK_ANDNU256(Bga, Bge));                    \
                                                                      \
  MLK_XOREQ256(A##be, De);                                            \
  MLK_ROL64IN256(Bka, A##be, 1);                                      \
  MLK_XOREQ256(A##gi, Di);                                            \
  MLK_ROL64IN256(Bke, A##gi, 6);                                      \
  MLK_XOREQ256(A##ko, Do);                                            \
  MLK_ROL64IN256(Bki, A##ko, 25);                                     \
  E##ka = MLK_XOR256(Bka, MLK_ANDNU256(Bke, Bki));                    \
  MLK_XOREQ256(A##mu, Du);                                            \
  MLK_ROL64IN256_8(Bko, A##mu);                                       \
  E##ke = MLK_XOR256(Bke, MLK_ANDNU256(Bki, Bko));                    \
  MLK_XOREQ256(A##sa, Da);                                            \
  MLK_ROL64IN256(Bku, A##sa, 18);                                     \
  E##ki = MLK_XOR256(Bki, MLK_ANDNU256(Bko, Bku));                    \
  E##ko = MLK_XOR256(Bko, MLK_ANDNU256(Bku, Bka));                    \
  E##ku = MLK_XOR256(Bku, MLK_ANDNU256(Bka, Bke));                    \
                                                                      \
  MLK_XOREQ256(A##bu, Du);                                            \
  MLK_ROL64IN256(Bma, A##bu, 27);                                     \
  MLK_XOREQ256(A##ga, Da);                                            \
  MLK_ROL64IN256(Bme, A##ga, 36);                                     \
  MLK_XOREQ256(A##ke, De);                                            \
  MLK_ROL64IN256(Bmi, A##ke, 10);                                     \
  E##ma = MLK_XOR256(Bma, MLK_ANDNU256(Bme, Bmi));                    \
  MLK_XOREQ256(A##mi, Di);                                            \
  MLK_ROL64IN256(Bmo, A##mi, 15);                                     \
  E##me = MLK_XOR256(Bme, MLK_ANDNU256(Bmi, Bmo));                    \
  MLK_XOREQ256(A##so, Do);                                            \
  MLK_ROL64IN256_56(Bmu, A##so);                                      \
  E##mi = MLK_XOR256(Bmi, MLK_ANDNU256(Bmo, Bmu));                    \
  E##mo = MLK_XOR256(Bmo, MLK_ANDNU256(Bmu, Bma));                    \
  E##mu = MLK_XOR256(Bmu, MLK_ANDNU256(Bma, Bme));                    \
                                                                      \
  MLK_XOREQ256(A##bi, Di);                                            \
  MLK_ROL64IN256(Bsa, A##bi, 62);                                     \
  MLK_XOREQ256(A##go, Do);                                            \
  MLK_ROL64IN256(Bse, A##go, 55);                                     \
  MLK_XOREQ256(A##ku, Du);                                            \
  MLK_ROL64IN256(Bsi, A##ku, 39);                                     \
  E##sa = MLK_XOR256(Bsa, MLK_ANDNU256(Bse, Bsi));                    \
  MLK_XOREQ256(A##ma, Da);                                            \
  MLK_ROL64IN256(Bso, A##ma, 41);                                     \
  E##se = MLK_XOR256(Bse, MLK_ANDNU256(Bsi, Bso));                    \
  MLK_XOREQ256(A##se, De);                                            \
  MLK_ROL64IN256(Bsu, A##se, 2);                                      \
  E##si = MLK_XOR256(Bsi, MLK_ANDNU256(Bso, Bsu));                    \
  E##so = MLK_XOR256(Bso, MLK_ANDNU256(Bsu, Bsa));                    \
  E##su = MLK_XOR256(Bsu, MLK_ANDNU256(Bsa, Bse));


static MLK_ALIGN const uint64_t keccakf1600RoundConstants[24] = {
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

#include <stdint.h>

#define MLK_COPY_FROM_STATE(X, state)                                       \
  do                                                                        \
  {                                                                         \
    const uint64_t *state64 = (const uint64_t *)(state);                    \
    __m256i _idx =                                                          \
        _mm256_set_epi64x((long long)&state64[75], (long long)&state64[50], \
                          (long long)&state64[25], (long long)&state64[0]); \
    X##ba = _mm256_i64gather_epi64((long long *)(0 * 8), _idx, 1);          \
    X##be = _mm256_i64gather_epi64((long long *)(1 * 8), _idx, 1);          \
    X##bi = _mm256_i64gather_epi64((long long *)(2 * 8), _idx, 1);          \
    X##bo = _mm256_i64gather_epi64((long long *)(3 * 8), _idx, 1);          \
    X##bu = _mm256_i64gather_epi64((long long *)(4 * 8), _idx, 1);          \
    X##ga = _mm256_i64gather_epi64((long long *)(5 * 8), _idx, 1);          \
    X##ge = _mm256_i64gather_epi64((long long *)(6 * 8), _idx, 1);          \
    X##gi = _mm256_i64gather_epi64((long long *)(7 * 8), _idx, 1);          \
    X##go = _mm256_i64gather_epi64((long long *)(8 * 8), _idx, 1);          \
    X##gu = _mm256_i64gather_epi64((long long *)(9 * 8), _idx, 1);          \
    X##ka = _mm256_i64gather_epi64((long long *)(10 * 8), _idx, 1);         \
    X##ke = _mm256_i64gather_epi64((long long *)(11 * 8), _idx, 1);         \
    X##ki = _mm256_i64gather_epi64((long long *)(12 * 8), _idx, 1);         \
    X##ko = _mm256_i64gather_epi64((long long *)(13 * 8), _idx, 1);         \
    X##ku = _mm256_i64gather_epi64((long long *)(14 * 8), _idx, 1);         \
    X##ma = _mm256_i64gather_epi64((long long *)(15 * 8), _idx, 1);         \
    X##me = _mm256_i64gather_epi64((long long *)(16 * 8), _idx, 1);         \
    X##mi = _mm256_i64gather_epi64((long long *)(17 * 8), _idx, 1);         \
    X##mo = _mm256_i64gather_epi64((long long *)(18 * 8), _idx, 1);         \
    X##mu = _mm256_i64gather_epi64((long long *)(19 * 8), _idx, 1);         \
    X##sa = _mm256_i64gather_epi64((long long *)(20 * 8), _idx, 1);         \
    X##se = _mm256_i64gather_epi64((long long *)(21 * 8), _idx, 1);         \
    X##si = _mm256_i64gather_epi64((long long *)(22 * 8), _idx, 1);         \
    X##so = _mm256_i64gather_epi64((long long *)(23 * 8), _idx, 1);         \
    X##su = _mm256_i64gather_epi64((long long *)(24 * 8), _idx, 1);         \
  } while (0);

#define MLK_SCATTER_STORE256(state, idx, v)                    \
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

#define MLK_COPY_TO_STATE(state, X)       \
  MLK_SCATTER_STORE256(state, 0, X##ba);  \
  MLK_SCATTER_STORE256(state, 1, X##be);  \
  MLK_SCATTER_STORE256(state, 2, X##bi);  \
  MLK_SCATTER_STORE256(state, 3, X##bo);  \
  MLK_SCATTER_STORE256(state, 4, X##bu);  \
  MLK_SCATTER_STORE256(state, 5, X##ga);  \
  MLK_SCATTER_STORE256(state, 6, X##ge);  \
  MLK_SCATTER_STORE256(state, 7, X##gi);  \
  MLK_SCATTER_STORE256(state, 8, X##go);  \
  MLK_SCATTER_STORE256(state, 9, X##gu);  \
  MLK_SCATTER_STORE256(state, 10, X##ka); \
  MLK_SCATTER_STORE256(state, 11, X##ke); \
  MLK_SCATTER_STORE256(state, 12, X##ki); \
  MLK_SCATTER_STORE256(state, 13, X##ko); \
  MLK_SCATTER_STORE256(state, 14, X##ku); \
  MLK_SCATTER_STORE256(state, 15, X##ma); \
  MLK_SCATTER_STORE256(state, 16, X##me); \
  MLK_SCATTER_STORE256(state, 17, X##mi); \
  MLK_SCATTER_STORE256(state, 18, X##mo); \
  MLK_SCATTER_STORE256(state, 19, X##mu); \
  MLK_SCATTER_STORE256(state, 20, X##sa); \
  MLK_SCATTER_STORE256(state, 21, X##se); \
  MLK_SCATTER_STORE256(state, 22, X##si); \
  MLK_SCATTER_STORE256(state, 23, X##so); \
  MLK_SCATTER_STORE256(state, 24, X##su);

#define MLK_COPY_STATE_VARIABLES(X, Y) \
  X##ba = Y##ba;                       \
  X##be = Y##be;                       \
  X##bi = Y##bi;                       \
  X##bo = Y##bo;                       \
  X##bu = Y##bu;                       \
  X##ga = Y##ga;                       \
  X##ge = Y##ge;                       \
  X##gi = Y##gi;                       \
  X##go = Y##go;                       \
  X##gu = Y##gu;                       \
  X##ka = Y##ka;                       \
  X##ke = Y##ke;                       \
  X##ki = Y##ki;                       \
  X##ko = Y##ko;                       \
  X##ku = Y##ku;                       \
  X##ma = Y##ma;                       \
  X##me = Y##me;                       \
  X##mi = Y##mi;                       \
  X##mo = Y##mo;                       \
  X##mu = Y##mu;                       \
  X##sa = Y##sa;                       \
  X##se = Y##se;                       \
  X##si = Y##si;                       \
  X##so = Y##so;                       \
  X##su = Y##su;

/* clang-format off */
#define MLK_ROUNDS24 \
    MLK_prepareTheta \
    MLK_thetaRhoPiChiIotaPrepareTheta( 0, A, E) \
    MLK_thetaRhoPiChiIotaPrepareTheta( 1, E, A) \
    MLK_thetaRhoPiChiIotaPrepareTheta( 2, A, E) \
    MLK_thetaRhoPiChiIotaPrepareTheta( 3, E, A) \
    MLK_thetaRhoPiChiIotaPrepareTheta( 4, A, E) \
    MLK_thetaRhoPiChiIotaPrepareTheta( 5, E, A) \
    MLK_thetaRhoPiChiIotaPrepareTheta( 6, A, E) \
    MLK_thetaRhoPiChiIotaPrepareTheta( 7, E, A) \
    MLK_thetaRhoPiChiIotaPrepareTheta( 8, A, E) \
    MLK_thetaRhoPiChiIotaPrepareTheta( 9, E, A) \
    MLK_thetaRhoPiChiIotaPrepareTheta(10, A, E) \
    MLK_thetaRhoPiChiIotaPrepareTheta(11, E, A) \
    MLK_thetaRhoPiChiIotaPrepareTheta(12, A, E) \
    MLK_thetaRhoPiChiIotaPrepareTheta(13, E, A) \
    MLK_thetaRhoPiChiIotaPrepareTheta(14, A, E) \
    MLK_thetaRhoPiChiIotaPrepareTheta(15, E, A) \
    MLK_thetaRhoPiChiIotaPrepareTheta(16, A, E) \
    MLK_thetaRhoPiChiIotaPrepareTheta(17, E, A) \
    MLK_thetaRhoPiChiIotaPrepareTheta(18, A, E) \
    MLK_thetaRhoPiChiIotaPrepareTheta(19, E, A) \
    MLK_thetaRhoPiChiIotaPrepareTheta(20, A, E) \
    MLK_thetaRhoPiChiIotaPrepareTheta(21, E, A) \
    MLK_thetaRhoPiChiIotaPrepareTheta(22, A, E) \
    MLK_thetaRhoPiChiIota(23, E, A)
/* clang-format on */

void mlk_keccakf1600x4_permute24(void *states)
{
  __m256i *statesAsLanes = (__m256i *)states;
  MLK_DECLARE_ABCDE MLK_COPY_FROM_STATE(A, statesAsLanes)
      MLK_ROUNDS24 MLK_COPY_TO_STATE(statesAsLanes, A)
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
#undef MLK_SNP_LANELENGTHINBYTES
#undef MLK_DECLARE_ABCDE
#undef MLK_prepareTheta
#undef MLK_thetaRhoPiChiIotaPrepareTheta
#undef MLK_thetaRhoPiChiIota
#undef MLK_COPY_FROM_STATE
#undef MLK_SCATTER_STORE256
#undef MLK_COPY_TO_STATE
#undef MLK_COPY_STATE_VARIABLES
#undef MLK_ROUNDS24
