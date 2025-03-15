/*
 * Copyright (c) 2024-2025 The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0
 */

#ifndef MLK_H
#define MLK_H
/*
 * Public API for mlkem-native
 *
 * This header defines the public API of a single build of mlkem-native.
 *
 * To use this header, make sure one of the following holds:
 *
 * - The config.h used for the build is available in the include paths.
 * - The values of MLK_BUILD_INFO_LVL and MLK_BUILD_INFO_NAMESPACE are set,
 * reflecting the security level (512/768/1024) and namespace of the build.
 *
 * This header specifies a build of mlkem-native for a fixed security level.
 * If you need multiple builds, e.g. to build a library offering multiple
 * security levels, you need multiple instances of this header. In this case,
 * make sure to rename or #undefine the header guard
 */

#include <stdint.h>
#include "sys.h"

/*************************** Build information ********************************/

/*
 * Provide security level (MLK_BUILD_INFO_LVL) and namespacing
 * (MLK_BUILD_INFO_NAMESPACE)
 *
 * By default, this is extracted from the configuration used for the build,
 * but you can also set it manually to avoid a dependency on the build config.
 */

/* Skip this if MLK_BUILD_INFO_LVL has already been set */
#if !defined(MLK_BUILD_INFO_LVL)

/* Option 1: Extract from config */
#if defined(MLK_CONFIG_FILE)
#include MLK_CONFIG_FILE
#else
#include "config.h"
#endif

#if MLKEM_K == 2
#define MLK_BUILD_INFO_LVL 512
#elif MLKEM_K == 3
#define MLK_BUILD_INFO_LVL 768
#elif MLKEM_K == 4
#define MLK_BUILD_INFO_LVL 1024
#else
#error MLKEM_K not set by config file
#endif

#ifndef MLK_NAMESPACE_PREFIX
#error MLK_NAMESPACE_PREFIX not set by config file
#endif

#if defined(MLK_MULTILEVEL_BUILD_WITH_SHARED) || \
    defined(MLK_MULTILEVEL_BUILD_NO_SHARED)
#define MLK_BUILD_INFO_CONCAT3_(x, y, z) x##y##_##z
#define MLK_BUILD_INFO_CONCAT3(x, y, z) MLK_BUILD_INFO_CONCAT_(x, y, z)
#define MLK_BUILD_INFO_NAMESPACE(sym) \
  MLK_BUILD_INFO_CONCAT3(MLK_NAMESPACE_PREFIX, MLK_BUILD_INFO_LVL, sym)
#else
#define MLK_BUILD_INFO_CONCAT2_(x, y) x##_##y
#define MLK_BUILD_INFO_CONCAT2(x, y) MLK_BUILD_INFO_CONCAT2_(x, y)
#define MLK_BUILD_INFO_NAMESPACE(sym) \
  MLK_BUILD_INFO_CONCAT2(MLK_NAMESPACE_PREFIX, sym)
#endif

#endif /* MLK_BUILD_INFO_LVL */

/* Option 2: Provide MLK_BUILD_INFO_LVL and MLK_BUILD_INFO_NAMESPACE manually */

/* #define MLK_BUILD_INFO_LVL            ADJUSTME */
/* #define MLK_BUILD_INFO_NAMESPACE(sym) ADJUSTME */

/******************************* Key sizes ************************************/

/* Sizes of cryptographic material, per level */
/* See mlke/common.h for the arithmetic expressions giving rise to these */
/* check-magic: off */
#define MLKEM512_SECRETKEYBYTES 1632
#define MLKEM512_PUBLICKEYBYTES 800
#define MLKEM512_CIPHERTEXTBYTES 768

#define MLKEM768_SECRETKEYBYTES 2400
#define MLKEM768_PUBLICKEYBYTES 1184
#define MLKEM768_CIPHERTEXTBYTES 1088

#define MLKEM1024_SECRETKEYBYTES 3168
#define MLKEM1024_PUBLICKEYBYTES 1568
#define MLKEM1024_CIPHERTEXTBYTES 1568
/* check-magic: on */

/* Size of randomness coins in bytes (level-independent) */
#define MLKEM_SYMBYTES 32
#define MLKEM512_SYMBYTES MLKEM_SYMBYTES
#define MLKEM768_SYMBYTES MLKEM_SYMBYTES
#define MLKEM1024_SYMBYTES MLKEM_SYMBYTES
/* Size of shared secret in bytes (level-independent) */
#define MLKEM_BYTES 32
#define MLKEM512_BYTES MLKEM_BYTES
#define MLKEM768_BYTES MLKEM_BYTES
#define MLKEM1024_BYTES MLKEM_BYTES

/* Sizes of cryptographic material, as a function of LVL=512,768,1024 */
#define MLKEM_SECRETKEYBYTES_(LVL) MLKEM##LVL##_SECRETKEYBYTES
#define MLKEM_PUBLICKEYBYTES_(LVL) MLKEM##LVL##_PUBLICKEYBYTES
#define MLKEM_CIPHERTEXTBYTES_(LVL) MLKEM##LVL##_CIPHERTEXTBYTES
#define MLKEM_SECRETKEYBYTES(LVL) MLKEM_SECRETKEYBYTES_(LVL)
#define MLKEM_PUBLICKEYBYTES(LVL) MLKEM_PUBLICKEYBYTES_(LVL)
#define MLKEM_CIPHERTEXTBYTES(LVL) MLKEM_CIPHERTEXTBYTES_(LVL)

/****************************** Function API **********************************/

#if defined(__GNUC__) || defined(clang)
#define MLK_MUST_CHECK_RETURN_VALUE __attribute__((warn_unused_result))
#else
#define MLK_MUST_CHECK_RETURN_VALUE
#endif

/*************************************************
 * Name:        crypto_kem_keypair_derand
 *
 * Description: Generates public and private key
 *              for CCA-secure ML-KEM key encapsulation mechanism
 *
 * Arguments:   - uint8_t pk[]: pointer to output public key, an array of
 *                 length MLKEM{512,768,1024}_PUBLICKEYBYTES bytes.
 *              - uint8_t sk[]: pointer to output private key, an array of
 *                  of MLKEM{512,768,1024}_SECRETKEYBYTES bytes.
 *              - uint8_t *coins: pointer to input randomness, an array of
 *                  2*MLKEM_SYMBYTES uniformly random bytes.
 *
 * Returns:     - 0: On success
 *              - -1: On PCT failure (if MLK_KEYGEN_PCT) is enabled.
 *
 * Specification: Implements [FIPS 203, Algorithm 16, ML-KEM.KeyGen_Internal]
 *
 **************************************************/
MLK_MUST_CHECK_RETURN_VALUE
int MLK_BUILD_INFO_NAMESPACE(keypair_derand)(
    uint8_t pk[MLKEM_PUBLICKEYBYTES(MLK_BUILD_INFO_LVL)],
    uint8_t sk[MLKEM_SECRETKEYBYTES(MLK_BUILD_INFO_LVL)],
    const uint8_t coins[2 * MLKEM_SYMBYTES]);

/*************************************************
 * Name:        crypto_kem_keypair
 *
 * Description: Generates public and private key
 *              for CCA-secure ML-KEM key encapsulation mechanism
 *
 * Arguments:   - uint8_t *pk: pointer to output public key, an array of
 *                 MLKEM{512,768,1024}_PUBLICKEYBYTES bytes.
 *              - uint8_t *sk: pointer to output private key, an array of
 *                 MLKEM{512,768,1024}_SECRETKEYBYTES bytes.
 *
 * Returns:     - 0: On success
 *              - -1: On PCT failure (if MLK_KEYGEN_PCT) is enabled.
 *
 * Specification: Implements [FIPS 203, Algorithm 19, ML-KEM.KeyGen]
 *
 **************************************************/
MLK_MUST_CHECK_RETURN_VALUE
int MLK_BUILD_INFO_NAMESPACE(keypair)(
    uint8_t pk[MLKEM_PUBLICKEYBYTES(MLK_BUILD_INFO_LVL)],
    uint8_t sk[MLKEM_SECRETKEYBYTES(MLK_BUILD_INFO_LVL)]);

/*************************************************
 * Name:        crypto_kem_enc_derand
 *
 * Description: Generates cipher text and shared
 *              secret for given public key
 *
 * Arguments:   - uint8_t *ct: pointer to output cipher text, an array of
 *                 MLKEM{512,768,1024}_CIPHERTEXTBYTES bytes.
 *              - uint8_t *ss: pointer to output shared secret, an array of
 *                 MLKEM_BYTES bytes.
 *              - const uint8_t *pk: pointer to input public key, an array of
 *                 MLKEM{512,768,1024}_PUBLICKEYBYTES bytes.
 *              - const uint8_t *coins: pointer to input randomness, an array of
 *                 MLKEM_SYMBYTES bytes.
 *
 * Returns: - 0 on success
 *          - -1 if the 'modulus check' [FIPS 203, Section 7.2]
 *            for the public key fails.
 *
 * Specification: Implements [FIPS 203, Algorithm 17, ML-KEM.Encaps_Internal]
 *
 **************************************************/
MLK_MUST_CHECK_RETURN_VALUE
int MLK_BUILD_INFO_NAMESPACE(enc_derand)(
    uint8_t ct[MLKEM_CIPHERTEXTBYTES(MLK_BUILD_INFO_LVL)],
    uint8_t ss[MLKEM_BYTES],
    const uint8_t pk[MLKEM_PUBLICKEYBYTES(MLK_BUILD_INFO_LVL)],
    const uint8_t coins[MLKEM_SYMBYTES]);

/*************************************************
 * Name:        crypto_kem_enc
 *
 * Description: Generates cipher text and shared
 *              secret for given public key
 *
 * Arguments:   - uint8_t *ct: pointer to output cipher text, an array of
 *                 MLKEM{512,768,1024}_CIPHERTEXTBYTES bytes.
 *              - uint8_t *ss: pointer to output shared secret, an array of
 *                 MLKEM_BYTES bytes.
 *              - const uint8_t *pk: pointer to input public key, an array of
 *                 MLKEM{512,768,1024}_PUBLICKEYBYTES bytes.
 *
 * Returns: - 0 on success
 *          - -1 if the 'modulus check' [FIPS 203, Section 7.2]
 *            for the public key fails.
 *
 * Specification: Implements [FIPS 203, Algorithm 20, ML-KEM.Encaps]
 *
 **************************************************/
MLK_MUST_CHECK_RETURN_VALUE
int MLK_BUILD_INFO_NAMESPACE(enc)(
    uint8_t ct[MLKEM_CIPHERTEXTBYTES(MLK_BUILD_INFO_LVL)],
    uint8_t ss[MLKEM_BYTES],
    const uint8_t pk[MLKEM_PUBLICKEYBYTES(MLK_BUILD_INFO_LVL)]);

/*************************************************
 * Name:        crypto_kem_dec
 *
 * Description: Generates shared secret for given
 *              cipher text and private key
 *
 * Arguments:   - uint8_t *ss: pointer to output shared secret, an array of
 *                 MLKEM_BYTES bytes.
 *              - const uint8_t *ct: pointer to input cipher text, an array of
 *                 MLKEM{512,768,1024}_CIPHERTEXTBYTES bytes.
 *              - const uint8_t *sk: pointer to input private key, an array of
 *                 MLKEM{512,768,1024}_SECRETKEYBYTES bytes.
 *
 * Returns: - 0 on success
 *          - -1 if the 'hash check' [FIPS 203, Section 7.3]
 *            for the secret key fails.
 *
 * Specification: Implements [FIPS 203, Algorithm 21, ML-KEM.Decaps]
 *
 **************************************************/
MLK_MUST_CHECK_RETURN_VALUE
int MLK_BUILD_INFO_NAMESPACE(dec)(
    uint8_t ss[MLKEM_BYTES],
    const uint8_t ct[MLKEM_CIPHERTEXTBYTES(MLK_BUILD_INFO_LVL)],
    const uint8_t sk[MLKEM_SECRETKEYBYTES(MLK_BUILD_INFO_LVL)]);


/* TODO: figure this out */
#define MLK_CONCAT_(x1, x2) x1##x2
#define MLK_CONCAT(x1, x2) MLK_CONCAT_(x1, x2)
#define MLK_BUILD_INFO_ADD_LEVEL(s) MLK_CONCAT(s, MLK_BUILD_INFO_LVL)
#define mlk_public_key MLK_BUILD_INFO_ADD_LEVEL(mlk_public_key)
#define mlk_secret_key MLK_BUILD_INFO_ADD_LEVEL(mlk_secret_key)
typedef struct
{
  uint8_t bytes[32768];
} MLK_ALIGN mlk_public_key;

typedef struct
{
  uint8_t bytes[32768];
} MLK_ALIGN mlk_secret_key;

void MLK_BUILD_INFO_NAMESPACE(marshal_pk)(
    uint8_t pk[MLKEM_PUBLICKEYBYTES(MLK_BUILD_INFO_LVL)],
    const mlk_public_key *pks);

MLK_MUST_CHECK_RETURN_VALUE
int MLK_BUILD_INFO_NAMESPACE(parse_pk)(
    mlk_public_key *pks,
    const uint8_t pk[MLKEM_PUBLICKEYBYTES(MLK_BUILD_INFO_LVL)]);

void MLK_BUILD_INFO_NAMESPACE(marshal_sk)(
    uint8_t sk[MLKEM_SECRETKEYBYTES(MLK_BUILD_INFO_LVL)],
    const mlk_secret_key *sks);

MLK_MUST_CHECK_RETURN_VALUE
int MLK_BUILD_INFO_NAMESPACE(parse_sk)(
    mlk_secret_key *sks,
    const uint8_t sk[MLKEM_SECRETKEYBYTES(MLK_BUILD_INFO_LVL)]);


MLK_MUST_CHECK_RETURN_VALUE
int MLK_BUILD_INFO_NAMESPACE(keypair_derand_struct)(
    mlk_public_key *pk, mlk_secret_key *sk,
    const uint8_t coins[2 * MLKEM_SYMBYTES]);

MLK_MUST_CHECK_RETURN_VALUE
int MLK_BUILD_INFO_NAMESPACE(keypair_struct)(mlk_public_key *pk,
                                             mlk_secret_key *sk);

MLK_MUST_CHECK_RETURN_VALUE
int MLK_BUILD_INFO_NAMESPACE(enc_derand_struct)(
    uint8_t ct[MLKEM_CIPHERTEXTBYTES(MLK_BUILD_INFO_LVL)],
    uint8_t ss[MLKEM_BYTES], const mlk_public_key *pk,
    const uint8_t coins[MLKEM_SYMBYTES]);

MLK_MUST_CHECK_RETURN_VALUE
int MLK_BUILD_INFO_NAMESPACE(enc_struct)(
    uint8_t ct[MLKEM_CIPHERTEXTBYTES(MLK_BUILD_INFO_LVL)],
    uint8_t ss[MLKEM_BYTES], const mlk_public_key *pk);

MLK_MUST_CHECK_RETURN_VALUE
int MLK_BUILD_INFO_NAMESPACE(dec_struct)(
    uint8_t ss[MLKEM_BYTES],
    const uint8_t ct[MLKEM_CIPHERTEXTBYTES(MLK_BUILD_INFO_LVL)],
    const mlk_secret_key *sk);

MLK_MUST_CHECK_RETURN_VALUE
int MLK_BUILD_INFO_NAMESPACE(sk_from_seed)(
    mlk_secret_key *sk, const uint8_t coins[2 * MLKEM_SYMBYTES]);

MLK_MUST_CHECK_RETURN_VALUE
int MLK_BUILD_INFO_NAMESPACE(pk_from_sk)(mlk_public_key *pk,
                                         mlk_secret_key *sk);


/****************************** Standard API *********************************/

/* If desired, export API in CRYPTO_xxx and crypto_kem_xxx format as used
 * e.g. by SUPERCOP and NIST.
 *
 * Remove this if you don't need it, or if you need multiple instances
 * of this header. */

#if !defined(MLK_BUILD_INFO_NO_STANDARD_API)
#define CRYPTO_SECRETKEYBYTES MLKEM_SECRETKEYBYTES(MLK_BUILD_INFO_LVL)
#define CRYPTO_PUBLICKEYBYTES MLKEM_PUBLICKEYBYTES(MLK_BUILD_INFO_LVL)
#define CRYPTO_CIPHERTEXTBYTES MLKEM_CIPHERTEXTBYTES(MLK_BUILD_INFO_LVL)

#define CRYPTO_SYMBYTES MLKEM_SYMBYTES
#define CRYPTO_BYTES MLKEM_BYTES

#define crypto_kem_keypair_derand MLK_BUILD_INFO_NAMESPACE(keypair_derand)
#define crypto_kem_keypair MLK_BUILD_INFO_NAMESPACE(keypair)
#define crypto_kem_enc_derand MLK_BUILD_INFO_NAMESPACE(enc_derand)
#define crypto_kem_enc MLK_BUILD_INFO_NAMESPACE(enc)
#define crypto_kem_dec MLK_BUILD_INFO_NAMESPACE(dec)

#define crypto_kem_marshal_pk MLK_BUILD_INFO_NAMESPACE(marshal_pk)
#define crypto_kem_parse_pk MLK_BUILD_INFO_NAMESPACE(parse_pk)
#define crypto_kem_marshal_sk MLK_BUILD_INFO_NAMESPACE(marshal_sk)
#define crypto_kem_parse_sk MLK_BUILD_INFO_NAMESPACE(parse_sk)
#define crypto_kem_keypair_derand_struct \
  MLK_BUILD_INFO_NAMESPACE(keypair_derand_struct)
#define crypto_kem_keypair_struct MLK_BUILD_INFO_NAMESPACE(keypair_struct)
#define crypto_kem_enc_derand_struct MLK_BUILD_INFO_NAMESPACE(enc_derand_struct)
#define crypto_kem_enc_struct MLK_BUILD_INFO_NAMESPACE(enc_struct)
#define crypto_kem_dec_struct MLK_BUILD_INFO_NAMESPACE(dec_struct)
#define crypto_kem_sk_from_seed MLK_BUILD_INFO_NAMESPACE(sk_from_seed)
#define crypto_kem_pk_from_sk MLK_BUILD_INFO_NAMESPACE(pk_from_sk)
#endif /* MLK_BUILD_INFO_NO_STANDARD_API */

/********************************* Cleanup ************************************/

/* Unset build information to allow multiple instances of this header.
 * Keep this commented out when using the standard API. */
/* #undef MLK_BUILD_INFO_LVL */
/* #undef MLK_BUILD_INFO_NAMESPACE */

#endif /* MLK_H */
