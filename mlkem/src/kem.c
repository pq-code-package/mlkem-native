/*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */

/* References
 * ==========
 *
 * - [FIPS140_3_IG]
 *   Implementation Guidance for FIPS 140-3 and the Cryptographic Module
 *   Validation Program
 *   National Institute of Standards and Technology
 *   https://csrc.nist.gov/projects/cryptographic-module-validation-program/fips-140-3-ig-announcements
 *
 * - [FIPS203]
 *   FIPS 203 Module-Lattice-Based Key-Encapsulation Mechanism Standard
 *   National Institute of Standards and Technology
 *   https://csrc.nist.gov/pubs/fips/203/final
 *
 * - [REF]
 *   CRYSTALS-Kyber C reference implementation
 *   Bos, Ducas, Kiltz, Lepoint, Lyubashevsky, Schanck, Schwabe, Seiler, Stehlé
 *   https://github.com/pq-crystals/kyber/tree/main/ref
 */

#include "kem.h"

#include "indcpa.h"
#include "randombytes.h"
#include "symmetric.h"
#include "verify.h"

/* Parameter set namespacing
 * This is to facilitate building multiple instances
 * of mlkem-native (e.g. with varying security levels)
 * within a single compilation unit. */
#define mlk_check_pct MLK_ADD_PARAM_SET(mlk_check_pct) MLK_CONTEXT_PARAMETERS_2
#define mlk_serialize_epp MLK_ADD_PARAM_SET(mlk_serialize_epp)
#define mlk_deserialize_epp MLK_ADD_PARAM_SET(mlk_deserialize_epp)
#define mlk_serialize_polyvec_16le MLK_ADD_PARAM_SET(mlk_serialize_polyvec_16le)
#define mlk_deserialize_polyvec_16le \
  MLK_ADD_PARAM_SET(mlk_deserialize_polyvec_16le)
/* End of parameter set namespacing */

/* Reference: Not implemented in the reference implementation @[REF]. */
MLK_EXTERNAL_API
MLK_MUST_CHECK_RETURN_VALUE
int mlk_kem_check_pk(const uint8_t pk[MLKEM_INDCCA_PUBLICKEYBYTES],
                     MLK_CONFIG_CONTEXT_PARAMETER_TYPE context)
{
  int ret = 0;
  MLK_ALLOC(p, mlk_polyvec, 1, context);
  MLK_ALLOC(p_reencoded, uint8_t, MLKEM_POLYVECBYTES, context);

  if (p == NULL || p_reencoded == NULL)
  {
    ret = MLK_ERR_OUT_OF_MEMORY;
    goto cleanup;
  }

  mlk_polyvec_frombytes(p, pk);
  mlk_polyvec_reduce(p);
  mlk_polyvec_tobytes(p_reencoded, p);

  /* We use a constant-time memcmp here to avoid having to
   * declassify the PK before the PCT has succeeded. */
  ret = mlk_ct_memcmp(pk, p_reencoded, MLKEM_POLYVECBYTES) ? MLK_ERR_FAIL : 0;

cleanup:
  /* Specification: Partially implements
   * @[FIPS203, Section 3.3, Destruction of intermediate values] */
  MLK_FREE(p_reencoded, uint8_t, MLKEM_POLYVECBYTES, context);
  MLK_FREE(p, mlk_polyvec, 1, context);
  return ret;
}


/* Reference: Not implemented in the reference implementation @[REF]. */
MLK_EXTERNAL_API
MLK_MUST_CHECK_RETURN_VALUE
int mlk_kem_check_sk(const uint8_t sk[MLKEM_INDCCA_SECRETKEYBYTES],
                     MLK_CONFIG_CONTEXT_PARAMETER_TYPE context)
{
  int ret = 0;
  MLK_ALLOC(test, uint8_t, MLKEM_SYMBYTES, context);

  if (test == NULL)
  {
    ret = MLK_ERR_OUT_OF_MEMORY;
    goto cleanup;
  }

  /*
   * The parts of `sk` being hashed and compared here are public, so
   * no public information is leaked through the runtime or the return value
   * of this function.
   */

  /* Declassify the public part of the secret key */
  MLK_CT_TESTING_DECLASSIFY(sk + MLKEM_INDCPA_SECRETKEYBYTES,
                            MLKEM_INDCCA_PUBLICKEYBYTES);
  MLK_CT_TESTING_DECLASSIFY(
      sk + MLKEM_INDCCA_SECRETKEYBYTES - 2 * MLKEM_SYMBYTES, MLKEM_SYMBYTES);

  mlk_hash_h(test, sk + MLKEM_INDCPA_SECRETKEYBYTES,
             MLKEM_INDCCA_PUBLICKEYBYTES);
  /* This doesn't have to be a constant-time memcmp, but it's the only place
   * in the library where a normal memcmp would be used otherwise, so for sake
   * of minimizing stdlib dependency, we use our constant-time one anyway. */
  ret = mlk_ct_memcmp(sk + MLKEM_INDCCA_SECRETKEYBYTES - 2 * MLKEM_SYMBYTES,
                      test, MLKEM_SYMBYTES)
            ? MLK_ERR_FAIL
            : 0;

cleanup:
  /* Specification: Partially implements
   * @[FIPS203, Section 3.3, Destruction of intermediate values] */
  MLK_FREE(test, uint8_t, MLKEM_SYMBYTES, context);
  return ret;
}

MLK_MUST_CHECK_RETURN_VALUE
static int mlk_check_pct(uint8_t const pk[MLKEM_INDCCA_PUBLICKEYBYTES],
                         uint8_t const sk[MLKEM_INDCCA_SECRETKEYBYTES],
                         MLK_CONFIG_CONTEXT_PARAMETER_TYPE context)
__contract__(
  requires(memory_no_alias(pk, MLKEM_INDCCA_PUBLICKEYBYTES))
  requires(memory_no_alias(sk, MLKEM_INDCCA_SECRETKEYBYTES))
  ensures(return_value == 0 || return_value == MLK_ERR_FAIL ||
          return_value == MLK_ERR_OUT_OF_MEMORY ||
          return_value == MLK_ERR_RNG_FAIL)
);

#if defined(MLK_CONFIG_KEYGEN_PCT)
/* Specification:
 * Partially implements 'Pairwise Consistency Test' @[FIPS140_3_IG, p.87] and
 * @[FIPS203, Section 7.1, Pairwise Consistency]. */

/* Reference: Not implemented in the reference implementation @[REF]. */
MLK_MUST_CHECK_RETURN_VALUE
static int mlk_check_pct(uint8_t const pk[MLKEM_INDCCA_PUBLICKEYBYTES],
                         uint8_t const sk[MLKEM_INDCCA_SECRETKEYBYTES],
                         MLK_CONFIG_CONTEXT_PARAMETER_TYPE context)
{
  int ret = 0;
  MLK_ALLOC(ct, uint8_t, MLKEM_INDCCA_CIPHERTEXTBYTES, context);
  MLK_ALLOC(ss_enc, uint8_t, MLKEM_SSBYTES, context);
  MLK_ALLOC(ss_dec, uint8_t, MLKEM_SSBYTES, context);

  if (ct == NULL || ss_enc == NULL || ss_dec == NULL)
  {
    ret = MLK_ERR_OUT_OF_MEMORY;
    goto cleanup;
  }

  ret = mlk_kem_enc(ct, ss_enc, pk, context);
  if (ret != 0)
  {
    goto cleanup;
  }

  ret = mlk_kem_dec(ss_dec, ct, sk, context);
  if (ret != 0)
  {
    goto cleanup;
  }

#if defined(MLK_CONFIG_KEYGEN_PCT_BREAKAGE_TEST)
  /* Deliberately break PCT for testing purposes */
  if (mlk_break_pct())
  {
    ss_enc[0] = ~ss_enc[0];
  }
#endif /* MLK_CONFIG_KEYGEN_PCT_BREAKAGE_TEST */

  ret = mlk_ct_memcmp(ss_enc, ss_dec, MLKEM_SSBYTES);
  /* The result of the PCT is public. */
  MLK_CT_TESTING_DECLASSIFY(&ret, sizeof(ret));

  if (ret != 0)
  {
    ret = MLK_ERR_FAIL;
  }

cleanup:

  /* Specification: Partially implements
   * @[FIPS203, Section 3.3, Destruction of intermediate values] */
  MLK_FREE(ss_dec, uint8_t, MLKEM_SSBYTES, context);
  MLK_FREE(ss_enc, uint8_t, MLKEM_SSBYTES, context);
  MLK_FREE(ct, uint8_t, MLKEM_INDCCA_CIPHERTEXTBYTES, context);
  return ret;
}
#else /* MLK_CONFIG_KEYGEN_PCT */
MLK_MUST_CHECK_RETURN_VALUE
static int mlk_check_pct(uint8_t const pk[MLKEM_INDCCA_PUBLICKEYBYTES],
                         uint8_t const sk[MLKEM_INDCCA_SECRETKEYBYTES],
                         MLK_CONFIG_CONTEXT_PARAMETER_TYPE context)
{
  /* Skip PCT */
  ((void)pk);
  ((void)sk);
#if defined(MLK_CONFIG_CONTEXT_PARAMETER)
  ((void)context);
#endif
  return 0;
}
#endif /* !MLK_CONFIG_KEYGEN_PCT */

/* Reference: `crypto_kem_keypair_derand()` in the reference implementation
 *            @[REF].
 *            - We optionally include PCT which is not present in
 *              the reference code. */
MLK_EXTERNAL_API
int mlk_kem_keypair_derand(uint8_t pk[MLKEM_INDCCA_PUBLICKEYBYTES],
                           uint8_t sk[MLKEM_INDCCA_SECRETKEYBYTES],
                           const uint8_t coins[2 * MLKEM_SYMBYTES],
                           MLK_CONFIG_CONTEXT_PARAMETER_TYPE context)
{
  int ret;

  ret = mlk_indcpa_keypair_derand(pk, sk, coins, context);
  if (ret != 0)
  {
    goto cleanup;
  }

  mlk_memcpy(sk + MLKEM_INDCPA_SECRETKEYBYTES, pk, MLKEM_INDCCA_PUBLICKEYBYTES);
  mlk_hash_h(sk + MLKEM_INDCCA_SECRETKEYBYTES - 2 * MLKEM_SYMBYTES, pk,
             MLKEM_INDCCA_PUBLICKEYBYTES);
  /* Value z for pseudo-random output on reject */
  mlk_memcpy(sk + MLKEM_INDCCA_SECRETKEYBYTES - MLKEM_SYMBYTES,
             coins + MLKEM_SYMBYTES, MLKEM_SYMBYTES);

  /* Declassify public key */
  MLK_CT_TESTING_DECLASSIFY(pk, MLKEM_INDCCA_PUBLICKEYBYTES);

  /* Pairwise Consistency Test (PCT) @[FIPS140_3_IG, p.87] */
  ret = mlk_check_pct(pk, sk, context);
  if (ret != 0)
  {
    goto cleanup;
  }

cleanup:
  if (ret != 0)
  {
    mlk_zeroize(pk, MLKEM_INDCCA_PUBLICKEYBYTES);
    mlk_zeroize(sk, MLKEM_INDCCA_SECRETKEYBYTES);
  }

  return ret;
}

#if !defined(MLK_CONFIG_NO_RANDOMIZED_API)
/* Reference: `crypto_kem_keypair()` in the reference implementation @[REF]
 *            - We zeroize the stack buffer */
MLK_EXTERNAL_API
int mlk_kem_keypair(uint8_t pk[MLKEM_INDCCA_PUBLICKEYBYTES],
                    uint8_t sk[MLKEM_INDCCA_SECRETKEYBYTES],
                    MLK_CONFIG_CONTEXT_PARAMETER_TYPE context)
{
  int ret = 0;
  MLK_ALLOC(coins, uint8_t, 2 * MLKEM_SYMBYTES, context);

  if (coins == NULL)
  {
    ret = MLK_ERR_OUT_OF_MEMORY;
    goto cleanup;
  }

  /* Acquire necessary randomness, and mark it as secret. */
  if (mlk_randombytes(coins, 2 * MLKEM_SYMBYTES) != 0)
  {
    ret = MLK_ERR_RNG_FAIL;
    goto cleanup;
  }

  MLK_CT_TESTING_SECRET(coins, 2 * MLKEM_SYMBYTES);

  ret = mlk_kem_keypair_derand(pk, sk, coins, context);

cleanup:
  /* Specification: Partially implements
   * @[FIPS203, Section 3.3, Destruction of intermediate values] */
  MLK_FREE(coins, uint8_t, 2 * MLKEM_SYMBYTES, context);
  return ret;
}
#endif /* !MLK_CONFIG_NO_RANDOMIZED_API */

/* Reference: `crypto_kem_enc_derand()` in the reference implementation @[REF]
 *            - We include public key check
 *            - We include stack buffer zeroization */
MLK_EXTERNAL_API
int mlk_kem_enc_derand(uint8_t ct[MLKEM_INDCCA_CIPHERTEXTBYTES],
                       uint8_t ss[MLKEM_SSBYTES],
                       const uint8_t pk[MLKEM_INDCCA_PUBLICKEYBYTES],
                       const uint8_t coins[MLKEM_SYMBYTES],
                       MLK_CONFIG_CONTEXT_PARAMETER_TYPE context)
{
  int ret = 0;
  MLK_ALLOC(buf, uint8_t, 2 * MLKEM_SYMBYTES, context);
  MLK_ALLOC(kr, uint8_t, 2 * MLKEM_SYMBYTES, context);

  if (buf == NULL || kr == NULL)
  {
    ret = MLK_ERR_OUT_OF_MEMORY;
    goto cleanup;
  }

  /* Specification: Implements @[FIPS203, Section 7.2, Modulus check] */
  ret = mlk_kem_check_pk(pk, context);
  if (ret != 0)
  {
    goto cleanup;
  }

  mlk_memcpy(buf, coins, MLKEM_SYMBYTES);

  /* Multitarget countermeasure for coins + contributory KEM */
  mlk_hash_h(buf + MLKEM_SYMBYTES, pk, MLKEM_INDCCA_PUBLICKEYBYTES);
  mlk_hash_g(kr, buf, 2 * MLKEM_SYMBYTES);

  /* coins are in kr+MLKEM_SYMBYTES */
  ret = mlk_indcpa_enc(ct, buf, pk, kr + MLKEM_SYMBYTES, context);
  if (ret != 0)
  {
    goto cleanup;
  }

  mlk_memcpy(ss, kr, MLKEM_SYMBYTES);

cleanup:
  /* Specification: Partially implements
   * @[FIPS203, Section 3.3, Destruction of intermediate values] */
  MLK_FREE(kr, uint8_t, 2 * MLKEM_SYMBYTES, context);
  MLK_FREE(buf, uint8_t, 2 * MLKEM_SYMBYTES, context);
  return ret;
}

#if !defined(MLK_CONFIG_NO_RANDOMIZED_API)
/* Reference: `crypto_kem_enc()` in the reference implementation @[REF]
 *            - We include stack buffer zeroization */
MLK_EXTERNAL_API
int mlk_kem_enc(uint8_t ct[MLKEM_INDCCA_CIPHERTEXTBYTES],
                uint8_t ss[MLKEM_SSBYTES],
                const uint8_t pk[MLKEM_INDCCA_PUBLICKEYBYTES],
                MLK_CONFIG_CONTEXT_PARAMETER_TYPE context)
{
  int ret = 0;
  MLK_ALLOC(coins, uint8_t, MLKEM_SYMBYTES, context);

  if (coins == NULL)
  {
    ret = MLK_ERR_OUT_OF_MEMORY;
    goto cleanup;
  }

  if (mlk_randombytes(coins, MLKEM_SYMBYTES) != 0)
  {
    ret = MLK_ERR_RNG_FAIL;
    goto cleanup;
  }

  MLK_CT_TESTING_SECRET(coins, MLKEM_SYMBYTES);

  ret = mlk_kem_enc_derand(ct, ss, pk, coins, context);

cleanup:
  /* Specification: Partially implements
   * @[FIPS203, Section 3.3, Destruction of intermediate values] */
  MLK_FREE(coins, uint8_t, MLKEM_SYMBYTES, context);
  return ret;
}
#endif /* !MLK_CONFIG_NO_RANDOMIZED_API */

#if defined(MLK_CONFIG_ENABLE_MLKEM_BRAID)

/* 4-bit packing for noise polynomial e2.
 * Coefficients in [-ETA2, ETA2] are stored as (ETA2 - x), fitting in 4 bits.
 * Two coefficients per byte (low nibble first). */
static void mlk_serialize_epp(uint8_t out[MLKEM_EPP_BYTES], const mlk_poly *p)
{
  unsigned j;
  for (j = 0; j < MLKEM_N / 2; j++)
  __loop__(
    assigns(j, memory_slice(out, MLKEM_EPP_BYTES))
    invariant(j <= MLKEM_N / 2)
    decreases(MLKEM_N / 2 - j))
  {
    uint8_t lo = (uint8_t)(MLKEM_ETA2 - p->coeffs[2 * j]);
    uint8_t hi = (uint8_t)(MLKEM_ETA2 - p->coeffs[2 * j + 1]);
    out[j] = (uint8_t)((lo & 0xF) | (uint8_t)(hi << 4));
  }
}

static void mlk_deserialize_epp(mlk_poly *p, const uint8_t in[MLKEM_EPP_BYTES])
{
  unsigned j;
  for (j = 0; j < MLKEM_N / 2; j++)
  __loop__(
    assigns(j, memory_slice(p, sizeof(mlk_poly)))
    invariant(j <= MLKEM_N / 2)
    invariant(array_abs_bound(p->coeffs, 0, 2 * j, 16))
    decreases(MLKEM_N / 2 - j))
  {
    p->coeffs[2 * j] = (int16_t)((int16_t)MLKEM_ETA2 - (int16_t)(in[j] & 0xF));
    p->coeffs[2 * j + 1] =
        (int16_t)((int16_t)MLKEM_ETA2 - (int16_t)(in[j] >> 4));
  }
}

/* 16-bit little-endian serialization for intermediate polyvec state.
 * Stores each int16_t coefficient as 2 bytes in LE order.
 * Coefficients must be non-negative (e.g., after reduce). */
static void mlk_serialize_polyvec_16le(uint8_t out[MLKEM_POLYVEC16_BYTES],
                                       const mlk_polyvec *v)
{
  unsigned i, j;
  for (i = 0; i < MLKEM_K; i++)
  __loop__(
    assigns(i, j, memory_slice(out, MLKEM_POLYVEC16_BYTES))
    invariant(i <= MLKEM_K)
    decreases(MLKEM_K - i))
  {
    for (j = 0; j < MLKEM_N; j++)
    __loop__(
      assigns(j, memory_slice(out, MLKEM_POLYVEC16_BYTES))
      invariant(j <= MLKEM_N)
      decreases(MLKEM_K - j))
    {
      uint16_t c = (uint16_t)v->vec[i].coeffs[j];
      out[i * MLKEM_POLY16_BYTES + 2 * j] = (uint8_t)(c & 0xFF);
      out[i * MLKEM_POLY16_BYTES + 2 * j + 1] = (uint8_t)(c >> 8);
    }
  }
}

static void mlk_deserialize_polyvec_16le(
    mlk_polyvec *v, const uint8_t in[MLKEM_POLYVEC16_BYTES])
{
  unsigned i, j;
  for (i = 0; i < MLKEM_K; i++)
  __loop__(
    assigns(i, j, memory_slice(v, sizeof(mlk_polyvec)))
    invariant(i <= MLKEM_K)
    decreases(MLKEM_K - i))
  {
    for (j = 0; j < MLKEM_N; j++)
    __loop__(
      assigns(j, memory_slice(v, sizeof(mlk_polyvec)))
      invariant(j <= MLKEM_N)
      decreases(MLKEM_K - j))
    {
      v->vec[i].coeffs[j] = mlk_cast_uint16_to_int16(
          (uint16_t)((unsigned)in[i * MLKEM_POLY16_BYTES + 2 * j] |
                     ((unsigned)in[i * MLKEM_POLY16_BYTES + 2 * j + 1] << 8)));
    }
  }
}

MLK_EXTERNAL_API
int mlk_kem_enc_derand_u(uint8_t ct_u[MLKEM_POLYVECCOMPRESSEDBYTES_DU],
                         uint8_t ss[MLKEM_SSBYTES],
                         uint8_t sp_serial[MLKEM_POLYVEC16_BYTES],
                         uint8_t epp_serial[MLKEM_EPP_BYTES],
                         const uint8_t seed[MLKEM_SYMBYTES],
                         const uint8_t hpk[MLKEM_SYMBYTES],
                         const uint8_t coins[MLKEM_SYMBYTES],
                         MLK_CONFIG_CONTEXT_PARAMETER_TYPE context)
{
  int ret = 0;
  MLK_ALLOC(buf, uint8_t, 2 * MLKEM_SYMBYTES, context);
  MLK_ALLOC(kr, uint8_t, 2 * MLKEM_SYMBYTES, context);
  MLK_ALLOC(sp, mlk_polyvec, 1, context);
  MLK_ALLOC(epp, mlk_poly, 1, context);
  MLK_ALLOC(sp_cache, mlk_polyvec_mulcache, 1, context);

  if (buf == NULL || kr == NULL || sp == NULL || epp == NULL ||
      sp_cache == NULL)
  {
    ret = MLK_ERR_OUT_OF_MEMORY;
    goto cleanup;
  }

  /* FO transform: (K, r) = G(coins || H(pk)) */
  mlk_memcpy(buf, coins, MLKEM_SYMBYTES);
  mlk_memcpy(buf + MLKEM_SYMBYTES, hpk, MLKEM_SYMBYTES);
  mlk_hash_g(kr, buf, 2 * MLKEM_SYMBYTES);

  /* Compute ct_u using derived randomness r */
  ret = mlk_indcpa_enc_u(ct_u, sp, epp, sp_cache, seed, kr + MLKEM_SYMBYTES,
                         context);
  if (ret != 0)
  {
    goto cleanup;
  }

  /* Reduce sp to unsigned canonical form before serialization */
  mlk_polyvec_reduce(sp);

  /* Serialize intermediate state */
  mlk_serialize_polyvec_16le(sp_serial, sp);
  mlk_serialize_epp(epp_serial, epp);

  /* Shared secret K = first MLKEM_SYMBYTES bytes of G output */
  mlk_memcpy(ss, kr, MLKEM_SYMBYTES);

cleanup:
  /* Specification: Partially implements
   * @[FIPS203, Section 3.3, Destruction of intermediate values] */
  MLK_FREE(sp_cache, mlk_polyvec_mulcache, 1, context);
  MLK_FREE(epp, mlk_poly, 1, context);
  MLK_FREE(sp, mlk_polyvec, 1, context);
  MLK_FREE(kr, uint8_t, 2 * MLKEM_SYMBYTES, context);
  MLK_FREE(buf, uint8_t, 2 * MLKEM_SYMBYTES, context);
  return ret;
}

MLK_EXTERNAL_API
int mlk_kem_enc_v(uint8_t ct_v[MLKEM_POLYCOMPRESSEDBYTES_DV],
                  const uint8_t sp_serial[MLKEM_POLYVEC16_BYTES],
                  const uint8_t epp_serial[MLKEM_EPP_BYTES],
                  const uint8_t coins[MLKEM_SYMBYTES],
                  const uint8_t ek_vector[MLKEM_POLYVECBYTES],
                  MLK_CONFIG_CONTEXT_PARAMETER_TYPE context)
{
  int ret = 0;
  MLK_ALLOC(sp, mlk_polyvec, 1, context);
  MLK_ALLOC(epp, mlk_poly, 1, context);
  MLK_ALLOC(sp_cache, mlk_polyvec_mulcache, 1, context);
  MLK_ALLOC(p, mlk_polyvec, 1, context);
  MLK_ALLOC(p_reencoded, uint8_t, MLKEM_POLYVECBYTES, context);

  if (sp == NULL || epp == NULL || sp_cache == NULL || p == NULL ||
      p_reencoded == NULL)
  {
    ret = MLK_ERR_OUT_OF_MEMORY;
    goto cleanup;
  }

  /* Specification: Implements @[FIPS203, Section 7.2, Modulus check]
   * on the public key vector ek_vector */
  mlk_polyvec_frombytes(p, ek_vector);
  mlk_polyvec_reduce(p);
  mlk_polyvec_tobytes(p_reencoded, p);
  ret = mlk_ct_memcmp(ek_vector, p_reencoded, MLKEM_POLYVECBYTES) ? MLK_ERR_FAIL
                                                                  : 0;
  if (ret != 0)
  {
    goto cleanup;
  }

  /* Deserialize intermediate state */
  mlk_deserialize_polyvec_16le(sp, sp_serial);
  mlk_deserialize_epp(epp, epp_serial);

  /* Compute mulcache for deserialized sp */
  mlk_polyvec_mulcache_compute(sp_cache, sp);

  ret = mlk_indcpa_enc_v(ct_v, sp, epp, sp_cache, coins, ek_vector, context);

cleanup:
  /* Specification: Partially implements
   * @[FIPS203, Section 3.3, Destruction of intermediate values] */
  MLK_FREE(p_reencoded, uint8_t, MLKEM_POLYVECBYTES, context);
  MLK_FREE(p, mlk_polyvec, 1, context);
  MLK_FREE(sp_cache, mlk_polyvec_mulcache, 1, context);
  MLK_FREE(epp, mlk_poly, 1, context);
  MLK_FREE(sp, mlk_polyvec, 1, context);
  return ret;
}

#endif /* MLK_CONFIG_ENABLE_MLKEM_BRAID */

/* Reference: `crypto_kem_dec()` in the reference implementation @[REF]
 *            - We include secret key check
 *            - We include stack buffer zeroization */
MLK_EXTERNAL_API
int mlk_kem_dec(uint8_t ss[MLKEM_SSBYTES],
                const uint8_t ct[MLKEM_INDCCA_CIPHERTEXTBYTES],
                const uint8_t sk[MLKEM_INDCCA_SECRETKEYBYTES],
                MLK_CONFIG_CONTEXT_PARAMETER_TYPE context)
{
  int ret = 0;
  uint8_t fail;
  const uint8_t *pk = sk + MLKEM_INDCPA_SECRETKEYBYTES;
  MLK_ALLOC(buf, uint8_t, 2 * MLKEM_SYMBYTES, context);
  MLK_ALLOC(kr, uint8_t, 2 * MLKEM_SYMBYTES, context);
  MLK_ALLOC(tmp, uint8_t, MLKEM_SYMBYTES + MLKEM_INDCCA_CIPHERTEXTBYTES,
            context);

  if (buf == NULL || kr == NULL || tmp == NULL)
  {
    ret = MLK_ERR_OUT_OF_MEMORY;
    goto cleanup;
  }

  /* Specification: Implements @[FIPS203, Section 7.3, Hash check] */
  ret = mlk_kem_check_sk(sk, context);
  if (ret != 0)
  {
    goto cleanup;
  }

  ret = mlk_indcpa_dec(buf, ct, sk, context);
  if (ret != 0)
  {
    goto cleanup;
  }

  /* Multitarget countermeasure for coins + contributory KEM */
  mlk_memcpy(buf + MLKEM_SYMBYTES,
             sk + MLKEM_INDCCA_SECRETKEYBYTES - 2 * MLKEM_SYMBYTES,
             MLKEM_SYMBYTES);
  mlk_hash_g(kr, buf, 2 * MLKEM_SYMBYTES);

  /* Recompute and compare ciphertext */
  /* coins are in kr+MLKEM_SYMBYTES */
  ret = mlk_indcpa_enc(tmp, buf, pk, kr + MLKEM_SYMBYTES, context);
  if (ret != 0)
  {
    goto cleanup;
  }

  fail = mlk_ct_memcmp(ct, tmp, MLKEM_INDCCA_CIPHERTEXTBYTES);

  /* Compute rejection key */
  mlk_memcpy(tmp, sk + MLKEM_INDCCA_SECRETKEYBYTES - MLKEM_SYMBYTES,
             MLKEM_SYMBYTES);
  mlk_memcpy(tmp + MLKEM_SYMBYTES, ct, MLKEM_INDCCA_CIPHERTEXTBYTES);
  mlk_hash_j(ss, tmp, MLKEM_SYMBYTES + MLKEM_INDCCA_CIPHERTEXTBYTES);

  /* Copy true key to return buffer if fail is 0 */
  mlk_ct_cmov_zero(ss, kr, MLKEM_SYMBYTES, fail);

cleanup:
  /* Specification: Partially implements
   * @[FIPS203, Section 3.3, Destruction of intermediate values] */
  MLK_FREE(tmp, uint8_t, MLKEM_SYMBYTES + MLKEM_INDCCA_CIPHERTEXTBYTES,
           context);
  MLK_FREE(kr, uint8_t, 2 * MLKEM_SYMBYTES, context);
  MLK_FREE(buf, uint8_t, 2 * MLKEM_SYMBYTES, context);

  return ret;
}

/* To facilitate single-compilation-unit (SCU) builds, undefine all macros.
 * Don't modify by hand -- this is auto-generated by scripts/autogen. */
#undef mlk_check_pct
#undef mlk_serialize_epp
#undef mlk_deserialize_epp
#undef mlk_serialize_polyvec_16le
#undef mlk_deserialize_polyvec_16le
