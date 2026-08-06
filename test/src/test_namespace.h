/*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */
#ifndef TEST_NAMESPACE_H
#define TEST_NAMESPACE_H

/* Build-config-independent aliases for the public API under test. */
#define MLK_TEST_CONCAT_(a, b) a##b
#define MLK_TEST_CONCAT(a, b) MLK_TEST_CONCAT_(a, b)
#define MLKEM_NAMESPACE(sym) \
  MLK_TEST_CONCAT(MLK_TEST_CONCAT(MLK_CONFIG_NAMESPACE_PREFIX, _), sym)

#define mlk_kem_keypair MLKEM_NAMESPACE(keypair)
#define mlk_kem_keypair_derand MLKEM_NAMESPACE(keypair_derand)
#define mlk_kem_enc MLKEM_NAMESPACE(enc)
#define mlk_kem_enc_derand MLKEM_NAMESPACE(enc_derand)
#define mlk_kem_check_pk MLKEM_NAMESPACE(check_pk)
#define mlk_kem_dec MLKEM_NAMESPACE(dec)
#define mlk_kem_check_sk MLKEM_NAMESPACE(check_sk)

/* Convenience abbreviations for the key, ciphertext and shared secret sizes.
 *
 * Ordinarily you know the parameter set you're working with, so you would
 * just use the level-specific constants directly, e.g. MLKEM512_PUBLICKEYBYTES,
 * MLKEM768_CIPHERTEXTBYTES, or MLKEM1024_SECRETKEYBYTES.
 *
 * The tests, however, are built for all three parameter sets (512, 768, 1024),
 * so we keep things generic by deriving the sizes from the configured
 * MLK_CONFIG_PARAMETER_SET. */
#define MLKEM_PK_BYTES MLKEM_PUBLICKEYBYTES(MLK_CONFIG_PARAMETER_SET)
#define MLKEM_SK_BYTES MLKEM_SECRETKEYBYTES(MLK_CONFIG_PARAMETER_SET)
#define MLKEM_CT_BYTES MLKEM_CIPHERTEXTBYTES(MLK_CONFIG_PARAMETER_SET)

#endif /* !TEST_NAMESPACE_H */
