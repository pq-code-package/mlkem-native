/*
 * Copyright (c) 2024 The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0
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
 * - copyFromState and copyToState operate on uninterleaved
 *   Keccak states in memory.
 */

#include "common.h"
#if defined(MLKEM_NATIVE_FIPS202_BACKEND_X86_64_XKCP)

#include <emmintrin.h>
#include <immintrin.h>
#include <smmintrin.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <wmmintrin.h>
#include "KeccakP-1600-times4-SnP.h"
#include "KeccakP-SIMD256-config.h"
#include "KeccakP-align.h"

#include "KeccakP-brg_endian.h"
#if (PLATFORM_BYTE_ORDER != IS_LITTLE_ENDIAN)
#error Expecting a little-endian platform
#endif

typedef unsigned long long int UINT64;
typedef __m256i V256;

#if defined(KeccakP1600times4_useAVX2)
#define ANDnu256(a, b) _mm256_andnot_si256(a, b)
#define CONST256(a) _mm256_load_si256((const V256 *)&(a))
#define CONST256_64(a) (V256) _mm256_broadcast_sd((const double *)(&a))
#define ROL64in256(d, a, o) \
  d = _mm256_or_si256(_mm256_slli_epi64(a, o), _mm256_srli_epi64(a, 64 - (o)))
#define ROL64in256_8(d, a) d = _mm256_shuffle_epi8(a, CONST256(rho8))
#define ROL64in256_56(d, a) d = _mm256_shuffle_epi8(a, CONST256(rho56))
static const UINT64 rho8[4] = {0x0605040302010007, 0x0E0D0C0B0A09080F,
                               0x1615141312111017, 0x1E1D1C1B1A19181F};
static const UINT64 rho56[4] = {0x0007060504030201, 0x080F0E0D0C0B0A09,
                                0x1017161514131211, 0x181F1E1D1C1B1A19};
#define STORE256(a, b) _mm256_store_si256((V256 *)&(a), b)
#define XOR256(a, b) _mm256_xor_si256(a, b)
#define XOReq256(a, b) a = _mm256_xor_si256(a, b)
#endif

#define SnP_laneLengthInBytes 8

#define declareABCDE            \
  V256 Aba, Abe, Abi, Abo, Abu; \
  V256 Aga, Age, Agi, Ago, Agu; \
  V256 Aka, Ake, Aki, Ako, Aku; \
  V256 Ama, Ame, Ami, Amo, Amu; \
  V256 Asa, Ase, Asi, Aso, Asu; \
  V256 Bba, Bbe, Bbi, Bbo, Bbu; \
  V256 Bga, Bge, Bgi, Bgo, Bgu; \
  V256 Bka, Bke, Bki, Bko, Bku; \
  V256 Bma, Bme, Bmi, Bmo, Bmu; \
  V256 Bsa, Bse, Bsi, Bso, Bsu; \
  V256 Ca, Ce, Ci, Co, Cu;      \
  V256 Ca1, Ce1, Ci1, Co1, Cu1; \
  V256 Da, De, Di, Do, Du;      \
  V256 Eba, Ebe, Ebi, Ebo, Ebu; \
  V256 Ega, Ege, Egi, Ego, Egu; \
  V256 Eka, Eke, Eki, Eko, Eku; \
  V256 Ema, Eme, Emi, Emo, Emu; \
  V256 Esa, Ese, Esi, Eso, Esu;

#define prepareTheta                                            \
  Ca = XOR256(Aba, XOR256(Aga, XOR256(Aka, XOR256(Ama, Asa)))); \
  Ce = XOR256(Abe, XOR256(Age, XOR256(Ake, XOR256(Ame, Ase)))); \
  Ci = XOR256(Abi, XOR256(Agi, XOR256(Aki, XOR256(Ami, Asi)))); \
  Co = XOR256(Abo, XOR256(Ago, XOR256(Ako, XOR256(Amo, Aso)))); \
  Cu = XOR256(Abu, XOR256(Agu, XOR256(Aku, XOR256(Amu, Asu))));

/*
 * --- Theta Rho Pi Chi Iota Prepare-theta
 * --- 64-bit lanes mapped to 64-bit words
 */
#define thetaRhoPiChiIotaPrepareTheta(i, A, E)                \
  ROL64in256(Ce1, Ce, 1);                                     \
  Da = XOR256(Cu, Ce1);                                       \
  ROL64in256(Ci1, Ci, 1);                                     \
  De = XOR256(Ca, Ci1);                                       \
  ROL64in256(Co1, Co, 1);                                     \
  Di = XOR256(Ce, Co1);                                       \
  ROL64in256(Cu1, Cu, 1);                                     \
  Do = XOR256(Ci, Cu1);                                       \
  ROL64in256(Ca1, Ca, 1);                                     \
  Du = XOR256(Co, Ca1);                                       \
                                                              \
  XOReq256(A##ba, Da);                                        \
  Bba = A##ba;                                                \
  XOReq256(A##ge, De);                                        \
  ROL64in256(Bbe, A##ge, 44);                                 \
  XOReq256(A##ki, Di);                                        \
  ROL64in256(Bbi, A##ki, 43);                                 \
  E##ba = XOR256(Bba, ANDnu256(Bbe, Bbi));                    \
  XOReq256(E##ba, CONST256_64(KeccakF1600RoundConstants[i])); \
  Ca = E##ba;                                                 \
  XOReq256(A##mo, Do);                                        \
  ROL64in256(Bbo, A##mo, 21);                                 \
  E##be = XOR256(Bbe, ANDnu256(Bbi, Bbo));                    \
  Ce = E##be;                                                 \
  XOReq256(A##su, Du);                                        \
  ROL64in256(Bbu, A##su, 14);                                 \
  E##bi = XOR256(Bbi, ANDnu256(Bbo, Bbu));                    \
  Ci = E##bi;                                                 \
  E##bo = XOR256(Bbo, ANDnu256(Bbu, Bba));                    \
  Co = E##bo;                                                 \
  E##bu = XOR256(Bbu, ANDnu256(Bba, Bbe));                    \
  Cu = E##bu;                                                 \
                                                              \
  XOReq256(A##bo, Do);                                        \
  ROL64in256(Bga, A##bo, 28);                                 \
  XOReq256(A##gu, Du);                                        \
  ROL64in256(Bge, A##gu, 20);                                 \
  XOReq256(A##ka, Da);                                        \
  ROL64in256(Bgi, A##ka, 3);                                  \
  E##ga = XOR256(Bga, ANDnu256(Bge, Bgi));                    \
  XOReq256(Ca, E##ga);                                        \
  XOReq256(A##me, De);                                        \
  ROL64in256(Bgo, A##me, 45);                                 \
  E##ge = XOR256(Bge, ANDnu256(Bgi, Bgo));                    \
  XOReq256(Ce, E##ge);                                        \
  XOReq256(A##si, Di);                                        \
  ROL64in256(Bgu, A##si, 61);                                 \
  E##gi = XOR256(Bgi, ANDnu256(Bgo, Bgu));                    \
  XOReq256(Ci, E##gi);                                        \
  E##go = XOR256(Bgo, ANDnu256(Bgu, Bga));                    \
  XOReq256(Co, E##go);                                        \
  E##gu = XOR256(Bgu, ANDnu256(Bga, Bge));                    \
  XOReq256(Cu, E##gu);                                        \
                                                              \
  XOReq256(A##be, De);                                        \
  ROL64in256(Bka, A##be, 1);                                  \
  XOReq256(A##gi, Di);                                        \
  ROL64in256(Bke, A##gi, 6);                                  \
  XOReq256(A##ko, Do);                                        \
  ROL64in256(Bki, A##ko, 25);                                 \
  E##ka = XOR256(Bka, ANDnu256(Bke, Bki));                    \
  XOReq256(Ca, E##ka);                                        \
  XOReq256(A##mu, Du);                                        \
  ROL64in256_8(Bko, A##mu);                                   \
  E##ke = XOR256(Bke, ANDnu256(Bki, Bko));                    \
  XOReq256(Ce, E##ke);                                        \
  XOReq256(A##sa, Da);                                        \
  ROL64in256(Bku, A##sa, 18);                                 \
  E##ki = XOR256(Bki, ANDnu256(Bko, Bku));                    \
  XOReq256(Ci, E##ki);                                        \
  E##ko = XOR256(Bko, ANDnu256(Bku, Bka));                    \
  XOReq256(Co, E##ko);                                        \
  E##ku = XOR256(Bku, ANDnu256(Bka, Bke));                    \
  XOReq256(Cu, E##ku);                                        \
                                                              \
  XOReq256(A##bu, Du);                                        \
  ROL64in256(Bma, A##bu, 27);                                 \
  XOReq256(A##ga, Da);                                        \
  ROL64in256(Bme, A##ga, 36);                                 \
  XOReq256(A##ke, De);                                        \
  ROL64in256(Bmi, A##ke, 10);                                 \
  E##ma = XOR256(Bma, ANDnu256(Bme, Bmi));                    \
  XOReq256(Ca, E##ma);                                        \
  XOReq256(A##mi, Di);                                        \
  ROL64in256(Bmo, A##mi, 15);                                 \
  E##me = XOR256(Bme, ANDnu256(Bmi, Bmo));                    \
  XOReq256(Ce, E##me);                                        \
  XOReq256(A##so, Do);                                        \
  ROL64in256_56(Bmu, A##so);                                  \
  E##mi = XOR256(Bmi, ANDnu256(Bmo, Bmu));                    \
  XOReq256(Ci, E##mi);                                        \
  E##mo = XOR256(Bmo, ANDnu256(Bmu, Bma));                    \
  XOReq256(Co, E##mo);                                        \
  E##mu = XOR256(Bmu, ANDnu256(Bma, Bme));                    \
  XOReq256(Cu, E##mu);                                        \
                                                              \
  XOReq256(A##bi, Di);                                        \
  ROL64in256(Bsa, A##bi, 62);                                 \
  XOReq256(A##go, Do);                                        \
  ROL64in256(Bse, A##go, 55);                                 \
  XOReq256(A##ku, Du);                                        \
  ROL64in256(Bsi, A##ku, 39);                                 \
  E##sa = XOR256(Bsa, ANDnu256(Bse, Bsi));                    \
  XOReq256(Ca, E##sa);                                        \
  XOReq256(A##ma, Da);                                        \
  ROL64in256(Bso, A##ma, 41);                                 \
  E##se = XOR256(Bse, ANDnu256(Bsi, Bso));                    \
  XOReq256(Ce, E##se);                                        \
  XOReq256(A##se, De);                                        \
  ROL64in256(Bsu, A##se, 2);                                  \
  E##si = XOR256(Bsi, ANDnu256(Bso, Bsu));                    \
  XOReq256(Ci, E##si);                                        \
  E##so = XOR256(Bso, ANDnu256(Bsu, Bsa));                    \
  XOReq256(Co, E##so);                                        \
  E##su = XOR256(Bsu, ANDnu256(Bsa, Bse));                    \
  XOReq256(Cu, E##su);


/*
 * --- Theta Rho Pi Chi Iota
 * --- 64-bit lanes mapped to 64-bit words
 */
#define thetaRhoPiChiIota(i, A, E)                            \
  ROL64in256(Ce1, Ce, 1);                                     \
  Da = XOR256(Cu, Ce1);                                       \
  ROL64in256(Ci1, Ci, 1);                                     \
  De = XOR256(Ca, Ci1);                                       \
  ROL64in256(Co1, Co, 1);                                     \
  Di = XOR256(Ce, Co1);                                       \
  ROL64in256(Cu1, Cu, 1);                                     \
  Do = XOR256(Ci, Cu1);                                       \
  ROL64in256(Ca1, Ca, 1);                                     \
  Du = XOR256(Co, Ca1);                                       \
                                                              \
  XOReq256(A##ba, Da);                                        \
  Bba = A##ba;                                                \
  XOReq256(A##ge, De);                                        \
  ROL64in256(Bbe, A##ge, 44);                                 \
  XOReq256(A##ki, Di);                                        \
  ROL64in256(Bbi, A##ki, 43);                                 \
  E##ba = XOR256(Bba, ANDnu256(Bbe, Bbi));                    \
  XOReq256(E##ba, CONST256_64(KeccakF1600RoundConstants[i])); \
  XOReq256(A##mo, Do);                                        \
  ROL64in256(Bbo, A##mo, 21);                                 \
  E##be = XOR256(Bbe, ANDnu256(Bbi, Bbo));                    \
  XOReq256(A##su, Du);                                        \
  ROL64in256(Bbu, A##su, 14);                                 \
  E##bi = XOR256(Bbi, ANDnu256(Bbo, Bbu));                    \
  E##bo = XOR256(Bbo, ANDnu256(Bbu, Bba));                    \
  E##bu = XOR256(Bbu, ANDnu256(Bba, Bbe));                    \
                                                              \
  XOReq256(A##bo, Do);                                        \
  ROL64in256(Bga, A##bo, 28);                                 \
  XOReq256(A##gu, Du);                                        \
  ROL64in256(Bge, A##gu, 20);                                 \
  XOReq256(A##ka, Da);                                        \
  ROL64in256(Bgi, A##ka, 3);                                  \
  E##ga = XOR256(Bga, ANDnu256(Bge, Bgi));                    \
  XOReq256(A##me, De);                                        \
  ROL64in256(Bgo, A##me, 45);                                 \
  E##ge = XOR256(Bge, ANDnu256(Bgi, Bgo));                    \
  XOReq256(A##si, Di);                                        \
  ROL64in256(Bgu, A##si, 61);                                 \
  E##gi = XOR256(Bgi, ANDnu256(Bgo, Bgu));                    \
  E##go = XOR256(Bgo, ANDnu256(Bgu, Bga));                    \
  E##gu = XOR256(Bgu, ANDnu256(Bga, Bge));                    \
                                                              \
  XOReq256(A##be, De);                                        \
  ROL64in256(Bka, A##be, 1);                                  \
  XOReq256(A##gi, Di);                                        \
  ROL64in256(Bke, A##gi, 6);                                  \
  XOReq256(A##ko, Do);                                        \
  ROL64in256(Bki, A##ko, 25);                                 \
  E##ka = XOR256(Bka, ANDnu256(Bke, Bki));                    \
  XOReq256(A##mu, Du);                                        \
  ROL64in256_8(Bko, A##mu);                                   \
  E##ke = XOR256(Bke, ANDnu256(Bki, Bko));                    \
  XOReq256(A##sa, Da);                                        \
  ROL64in256(Bku, A##sa, 18);                                 \
  E##ki = XOR256(Bki, ANDnu256(Bko, Bku));                    \
  E##ko = XOR256(Bko, ANDnu256(Bku, Bka));                    \
  E##ku = XOR256(Bku, ANDnu256(Bka, Bke));                    \
                                                              \
  XOReq256(A##bu, Du);                                        \
  ROL64in256(Bma, A##bu, 27);                                 \
  XOReq256(A##ga, Da);                                        \
  ROL64in256(Bme, A##ga, 36);                                 \
  XOReq256(A##ke, De);                                        \
  ROL64in256(Bmi, A##ke, 10);                                 \
  E##ma = XOR256(Bma, ANDnu256(Bme, Bmi));                    \
  XOReq256(A##mi, Di);                                        \
  ROL64in256(Bmo, A##mi, 15);                                 \
  E##me = XOR256(Bme, ANDnu256(Bmi, Bmo));                    \
  XOReq256(A##so, Do);                                        \
  ROL64in256_56(Bmu, A##so);                                  \
  E##mi = XOR256(Bmi, ANDnu256(Bmo, Bmu));                    \
  E##mo = XOR256(Bmo, ANDnu256(Bmu, Bma));                    \
  E##mu = XOR256(Bmu, ANDnu256(Bma, Bme));                    \
                                                              \
  XOReq256(A##bi, Di);                                        \
  ROL64in256(Bsa, A##bi, 62);                                 \
  XOReq256(A##go, Do);                                        \
  ROL64in256(Bse, A##go, 55);                                 \
  XOReq256(A##ku, Du);                                        \
  ROL64in256(Bsi, A##ku, 39);                                 \
  E##sa = XOR256(Bsa, ANDnu256(Bse, Bsi));                    \
  XOReq256(A##ma, Da);                                        \
  ROL64in256(Bso, A##ma, 41);                                 \
  E##se = XOR256(Bse, ANDnu256(Bsi, Bso));                    \
  XOReq256(A##se, De);                                        \
  ROL64in256(Bsu, A##se, 2);                                  \
  E##si = XOR256(Bsi, ANDnu256(Bso, Bsu));                    \
  E##so = XOR256(Bso, ANDnu256(Bsu, Bsa));                    \
  E##su = XOR256(Bsu, ANDnu256(Bsa, Bse));


static ALIGN(KeccakP1600times4_statesAlignment) const UINT64
    KeccakF1600RoundConstants[24] = {
        0x0000000000000001ULL, 0x0000000000008082ULL, 0x800000000000808aULL,
        0x8000000080008000ULL, 0x000000000000808bULL, 0x0000000080000001ULL,
        0x8000000080008081ULL, 0x8000000000008009ULL, 0x000000000000008aULL,
        0x0000000000000088ULL, 0x0000000080008009ULL, 0x000000008000000aULL,
        0x000000008000808bULL, 0x800000000000008bULL, 0x8000000000008089ULL,
        0x8000000000008003ULL, 0x8000000000008002ULL, 0x8000000000000080ULL,
        0x000000000000800aULL, 0x800000008000000aULL, 0x8000000080008081ULL,
        0x8000000000008080ULL, 0x0000000080000001ULL, 0x8000000080008008ULL};

#include <stdint.h>

#define copyFromState(X, state)                                             \
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

#define SCATTER_STORE256(state, idx, v)                        \
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

#define copyToState(state, X)         \
  SCATTER_STORE256(state, 0, X##ba);  \
  SCATTER_STORE256(state, 1, X##be);  \
  SCATTER_STORE256(state, 2, X##bi);  \
  SCATTER_STORE256(state, 3, X##bo);  \
  SCATTER_STORE256(state, 4, X##bu);  \
  SCATTER_STORE256(state, 5, X##ga);  \
  SCATTER_STORE256(state, 6, X##ge);  \
  SCATTER_STORE256(state, 7, X##gi);  \
  SCATTER_STORE256(state, 8, X##go);  \
  SCATTER_STORE256(state, 9, X##gu);  \
  SCATTER_STORE256(state, 10, X##ka); \
  SCATTER_STORE256(state, 11, X##ke); \
  SCATTER_STORE256(state, 12, X##ki); \
  SCATTER_STORE256(state, 13, X##ko); \
  SCATTER_STORE256(state, 14, X##ku); \
  SCATTER_STORE256(state, 15, X##ma); \
  SCATTER_STORE256(state, 16, X##me); \
  SCATTER_STORE256(state, 17, X##mi); \
  SCATTER_STORE256(state, 18, X##mo); \
  SCATTER_STORE256(state, 19, X##mu); \
  SCATTER_STORE256(state, 20, X##sa); \
  SCATTER_STORE256(state, 21, X##se); \
  SCATTER_STORE256(state, 22, X##si); \
  SCATTER_STORE256(state, 23, X##so); \
  SCATTER_STORE256(state, 24, X##su);

#define copyStateVariables(X, Y) \
  X##ba = Y##ba;                 \
  X##be = Y##be;                 \
  X##bi = Y##bi;                 \
  X##bo = Y##bo;                 \
  X##bu = Y##bu;                 \
  X##ga = Y##ga;                 \
  X##ge = Y##ge;                 \
  X##gi = Y##gi;                 \
  X##go = Y##go;                 \
  X##gu = Y##gu;                 \
  X##ka = Y##ka;                 \
  X##ke = Y##ke;                 \
  X##ki = Y##ki;                 \
  X##ko = Y##ko;                 \
  X##ku = Y##ku;                 \
  X##ma = Y##ma;                 \
  X##me = Y##me;                 \
  X##mi = Y##mi;                 \
  X##mo = Y##mo;                 \
  X##mu = Y##mu;                 \
  X##sa = Y##sa;                 \
  X##se = Y##se;                 \
  X##si = Y##si;                 \
  X##so = Y##so;                 \
  X##su = Y##su;

#ifdef KeccakP1600times4_fullUnrolling
#define FullUnrolling
#else
#define Unrolling KeccakP1600times4_unrolling
#endif
#include "KeccakP-1600-unrolling.macros"

void KeccakP1600times4_PermuteAll_24rounds(void *states)
{
  V256 *statesAsLanes = (V256 *)states;
  declareABCDE
#ifndef KeccakP1600times4_fullUnrolling
      unsigned i;
#endif

  copyFromState(A, statesAsLanes) rounds24 copyToState(statesAsLanes, A)
}

#else

/* Dummy constant to keep compiler happy despite empty CU */
#define empty_cu_avx2_keccakx4 FIPS202_NAMESPACE(empty_cu_avx2_keccakx4)
int empty_cu_avx2_keccakx4;

#endif /* MLKEM_NATIVE_FIPS202_BACKEND_X86_64_XKCP */
