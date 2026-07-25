/*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "../../mlkem/src/common.h"

#include "../../mlkem/mlkem_native.h"
#include "../src/test_namespace.h"

/* The test-case handlers below return void, so a failed check must exit(). */
#define MLK_TEST_CHECK_EXIT
#include "../src/test_common.h"

#define USAGE \
  "acvp_mlkem{lvl} [encapDecap|keyGen] [AFT|VAL] {test specific arguments}"
#define ENCAPS_USAGE "acvp_mlkem{lvl} encapDecap AFT encaps ek=HEX m=HEX"
#define DECAPS_USAGE "acvp_mlkem{lvl} encapDecap VAL decaps dk=HEX c=HEX"
#define KEYGEN_USAGE "acvp_mlkem{lvl} keyGen AFT z=HEX d=HEX"
#define ENCAPS_KEY_CHECK_USAGE \
  "acvp_mlkem{lvl} encapDecap VAL encapsulationKeyCheck ek=HEX"
#define DECAPS_KEY_CHECK_USAGE \
  "acvp_mlkem{lvl} encapDecap VAL decapsulationKeyCheck dk=HEX"


typedef enum
{
  encapDecap,
  keyGen
} acvp_mode;

typedef enum
{
  AFT,
  VAL
} acvp_type;

typedef enum
{
  encapsulation,
  decapsulation,
  encapsulationKeyCheck,
  decapsulationKeyCheck
} acvp_encapDecap_function;

/* Decode hex character [0-9A-Fa-f] into 0-15 */
static unsigned char decode_hex_char(char hex)
{
  if (hex >= '0' && hex <= '9')
  {
    return (unsigned char)(hex - '0');
  }
  else if (hex >= 'A' && hex <= 'F')
  {
    return (unsigned char)(10 + (unsigned char)(hex - 'A'));
  }
  else if (hex >= 'a' && hex <= 'f')
  {
    return (unsigned char)(10 + (unsigned char)(hex - 'a'));
  }
  else
  {
    return 0xFF;
  }
}

static int decode_hex(const char *prefix, unsigned char *out, size_t out_len,
                      const char *hex)
{
  size_t i;
  size_t hex_len = strlen(hex);
  size_t prefix_len = strlen(prefix);
  /*
   * Check that hex starts with `prefix=`
   * Use memcmp, not strcmp
   */
  if (hex_len < prefix_len + 1 || memcmp(prefix, hex, prefix_len) != 0 ||
      hex[prefix_len] != '=')
  {
    goto hex_usage;
  }

  hex += prefix_len + 1;
  hex_len -= prefix_len + 1;

  if (hex_len != 2 * out_len)
  {
    return 1;
  }

  for (i = 0; i < out_len; i++, hex += 2, out++)
  {
    unsigned hex0 = decode_hex_char(hex[0]);
    unsigned hex1 = decode_hex_char(hex[1]);
    if (hex0 == 0xFF || hex1 == 0xFF)
    {
      goto hex_usage;
    }

    *out = (unsigned char)((hex0 << 4) | hex1);
  }

  return 0;

hex_usage:
  fprintf(stderr,
          "Argument %s invalid: Expected argument of the form '%s=HEX' with "
          "HEX being a hex encoding of %u bytes\n",
          hex, prefix, (unsigned)out_len);
  return 1;
}

#if !defined(MLK_CONFIG_NO_DECAPS_API)
/*
 * Decode the decapsulation-key argument into dk. It is either the expanded
 * key ("dk=HEX", keyFormat 'expanded') or a seed d||z to expand via keyGen
 * ("seed=HEX", keyFormat 'seed'). Returns 0 on success, 1 on failure.
 * MLK_NOINLINE keeps the keyGen scratch (ek) out of the caller's (main's)
 * stack frame; under -fsanitize=undefined it would not share slots and would
 * overflow AVR RAM.
 */
static MLK_NOINLINE int decode_dk(const char *arg,
                                  unsigned char dk[MLKEM_SK_BYTES])
{
  size_t seed_len = strlen("seed=");

  /* Prefix check via memcmp; strncmp is unavailable on baremetal builds. */
  if (strlen(arg) >= seed_len && memcmp(arg, "seed=", seed_len) == 0)
  {
#if !defined(MLK_CONFIG_NO_KEYPAIR_API)
    unsigned char ek[MLKEM_PK_BYTES];
    unsigned char coins[2 * MLKEM_SYMBYTES];
    if (decode_hex("seed", coins, sizeof(coins), arg) != 0)
    {
      return 1;
    }
    if (mlk_kem_keypair_derand(ek, dk, coins) != 0)
    {
      fprintf(stderr, "Failed to expand seed into decapsulation key\n");
      return 1;
    }
    return 0;
#else  /* !MLK_CONFIG_NO_KEYPAIR_API */
    fprintf(stderr, "seed key format requires the keyGen API\n");
    return 1;
#endif /* MLK_CONFIG_NO_KEYPAIR_API */
  }
  return decode_hex("dk", dk, MLKEM_SK_BYTES, arg);
}
#endif /* !MLK_CONFIG_NO_DECAPS_API */

static void print_hex(const char *name, const unsigned char *raw, size_t len)
{
  if (name != NULL)
  {
    printf("%s=", name);
  }
  for (; len > 0; len--, raw++)
  {
    printf("%02X", *raw);
  }
  printf("\n");
}

/* The test-case handlers below are MLK_NOINLINE so their large key buffers
 * stay in short-lived frames. This can reduce stack usage in some
 * environments, e.g. AVR. */
#if !defined(MLK_CONFIG_NO_ENCAPS_API)
static MLK_NOINLINE void acvp_mlkem_encapDecp_AFT_encapsulation(
    unsigned char const ek[MLKEM_PK_BYTES],
    unsigned char const m[MLKEM_SYMBYTES])
{
  unsigned char ct[MLKEM_CT_BYTES];
  unsigned char ss[MLKEM_BYTES];

  CHECK_ERR(mlk_kem_enc_derand(ct, ss, ek, m), 0);

  print_hex("c", ct, sizeof(ct));
  print_hex("k", ss, sizeof(ss));
}

static MLK_NOINLINE void acvp_mlkem_encapDecp_VAL_encapsulationKeyCheck(
    unsigned char const ek[MLKEM_PK_BYTES])
{
  int rc = 0;
  rc = (mlk_kem_check_pk(ek) == 0) ? 1 : 0;
  printf("testPassed=%d\n", rc);
}
#endif /* !MLK_CONFIG_NO_ENCAPS_API */

#if !defined(MLK_CONFIG_NO_DECAPS_API)
static MLK_NOINLINE void acvp_mlkem_encapDecp_VAL_decapsulation(
    unsigned char const dk[MLKEM_SK_BYTES],
    unsigned char const c[MLKEM_CT_BYTES])
{
  unsigned char ss[MLKEM_BYTES];

  CHECK_ERR(mlk_kem_dec(ss, c, dk), 0);

  print_hex("k", ss, sizeof(ss));
}

static MLK_NOINLINE void acvp_mlkem_encapDecp_VAL_decapsulationKeyCheck(
    unsigned char const dk[MLKEM_SK_BYTES])
{
  int rc = 0;
  rc = (mlk_kem_check_sk(dk) == 0) ? 1 : 0;
  printf("testPassed=%d\n", rc);
}
#endif /* !MLK_CONFIG_NO_DECAPS_API */

#if !defined(MLK_CONFIG_NO_KEYPAIR_API)
static MLK_NOINLINE void acvp_mlkem_keyGen_AFT(
    unsigned char const z[MLKEM_SYMBYTES],
    unsigned char const d[MLKEM_SYMBYTES])
{
  unsigned char ek[MLKEM_PK_BYTES];
  unsigned char dk[MLKEM_SK_BYTES];

  unsigned char zd[2 * MLKEM_SYMBYTES];
  memcpy(zd, d, MLKEM_SYMBYTES);
  memcpy(zd + MLKEM_SYMBYTES, z, MLKEM_SYMBYTES);

  CHECK_ERR(mlk_kem_keypair_derand(ek, dk, zd), 0);

  print_hex("ek", ek, sizeof(ek));
  print_hex("dk", dk, sizeof(dk));
}
#endif /* !MLK_CONFIG_NO_KEYPAIR_API */

/* Print supported ACVP modes and functions and exit (used by acvp_client.py).
 * ML-KEM's ACVP schema bundles encapsulation and decapsulation into the
 * "encapDecap" mode; individual test functions (encapsulation vs
 * decapsulation, plus the *KeyCheck helpers) may still be disabled
 * independently. We advertise each function that is compiled in. */
static void print_info(void)
{
#if !defined(MLK_CONFIG_NO_KEYPAIR_API)
  printf("keyGen\n");
#endif
#if !defined(MLK_CONFIG_NO_ENCAPS_API)
  printf("encapsulation\n");
  printf("encapsulationKeyCheck\n");
#endif
#if !defined(MLK_CONFIG_NO_DECAPS_API)
  printf("decapsulation\n");
  printf("decapsulationKeyCheck\n");
#endif
}

/* Prototype for a re-#define'd main, to satisfy -Wmissing-prototypes. */
#if defined(main)
int main(int argc, char *argv[]);
#endif
int main(int argc, char *argv[])
{
  acvp_mode mode;
  acvp_type type;

  if (argc == 0)
  {
    goto usage;
  }
  argc--, argv++;

  /* Parse mode: "encapDecap" or "keyGen" or "--info" */
  if (argc == 0)
  {
    goto usage;
  }

  if (strcmp(*argv, "--info") == 0)
  {
    print_info();
    return 0;
  }

  if (strcmp(*argv, "encapDecap") == 0)
  {
    mode = encapDecap;
  }
  else if (strcmp(*argv, "keyGen") == 0)
  {
    mode = keyGen;
  }
  else
  {
    goto usage;
  }
  argc--, argv++;

  /* Parse test type: "AFT" (Algorithm Functional Test) or "VAL" (Validation) */
  if (argc == 0)
  {
    goto usage;
  }

  if (strcmp(*argv, "AFT") == 0)
  {
    type = AFT;
  }
  else if (strcmp(*argv, "VAL") == 0)
  {
    type = VAL;
  }
  else
  {
    goto usage;
  }
  argc--, argv++;

  /* Case: encapDecap */
  switch (mode)
  {
    case encapDecap:
    {
      acvp_encapDecap_function encapDecap_function;
      /* Parse function: "encapsulation" or "decapsulation" */
      if (argc == 0)
      {
        goto usage;
      }

      if (strcmp(*argv, "encapsulation") == 0)
      {
        encapDecap_function = encapsulation;
      }
      else if (strcmp(*argv, "decapsulation") == 0)
      {
        encapDecap_function = decapsulation;
      }
      else if (strcmp(*argv, "encapsulationKeyCheck") == 0)
      {
        encapDecap_function = encapsulationKeyCheck;
      }
      else if (strcmp(*argv, "decapsulationKeyCheck") == 0)
      {
        encapDecap_function = decapsulationKeyCheck;
      }
      else
      {
        goto usage;
      }
      argc--, argv++;

      switch (encapDecap_function)
      {
#if !defined(MLK_CONFIG_NO_ENCAPS_API)
        case encapsulation:
        {
          unsigned char ek[MLKEM_PK_BYTES];
          unsigned char m[MLKEM_SYMBYTES];
          /* Encapsulation only for "AFT" */
          if (type != AFT)
          {
            goto encaps_usage;
          }

          /* Parse ek */
          if (argc == 0 || decode_hex("ek", ek, sizeof(ek), *argv) != 0)
          {
            goto encaps_usage;
          }
          argc--, argv++;

          /* Parse m */
          if (argc == 0 || decode_hex("m", m, sizeof(m), *argv) != 0)
          {
            goto encaps_usage;
          }
          argc--, argv++;

          /* Call function under test */
          acvp_mlkem_encapDecp_AFT_encapsulation(ek, m);
          break;
        }
#endif /* !MLK_CONFIG_NO_ENCAPS_API */
#if !defined(MLK_CONFIG_NO_DECAPS_API)
        case decapsulation:
        {
          unsigned char dk[MLKEM_SK_BYTES];
          unsigned char c[MLKEM_CT_BYTES];
          /* Decapsulation only for "VAL" */
          if (type != VAL)
          {
            goto decaps_usage;
          }

          /* Parse dk (expanded key, or a seed to expand) */
          if (argc == 0 || decode_dk(*argv, dk) != 0)
          {
            goto decaps_usage;
          }
          argc--, argv++;

          /* Parse c */
          if (argc == 0 || decode_hex("c", c, sizeof(c), *argv) != 0)
          {
            goto decaps_usage;
          }
          argc--, argv++;

          /* Call function under test */
          acvp_mlkem_encapDecp_VAL_decapsulation(dk, c);
          break;
        }
#endif /* !MLK_CONFIG_NO_DECAPS_API */
#if !defined(MLK_CONFIG_NO_ENCAPS_API)
        case encapsulationKeyCheck:
        {
          unsigned char ek[MLKEM_PK_BYTES];
          /* encapsulationKeyCheck only for "VAL" */
          if (type != VAL || argc == 0)
          {
            goto encapsulationKeyCheck_usage;
          }

          /* Parse ek */
          if (decode_hex("ek", ek, sizeof(ek), *argv) != 0)
          {
            /*
              ACVP 1.1.0.40+ {en, de}capsulationKeyCheck test cases test keys of
              incorrect length. The mlkem-native API does not allow passing keys
              of incorrect length. We, hence, fail during decoding instead.
            */
            printf("testPassed=0\n");
            return 0;
          }
          argc--, argv++;

          /* Call function under test */
          acvp_mlkem_encapDecp_VAL_encapsulationKeyCheck(ek);
          break;
        }
#endif /* !MLK_CONFIG_NO_ENCAPS_API */
#if !defined(MLK_CONFIG_NO_DECAPS_API)
        case decapsulationKeyCheck:
        {
          unsigned char dk[MLKEM_SK_BYTES];
          /* Encapsulation only for "VAL" */
          if (type != VAL || argc == 0)
          {
            goto decapsulationKeyCheck_usage;
          }

          /* Parse dk */
          if (decode_hex("dk", dk, sizeof(dk), *argv) != 0)
          {
            /*
              ACVP 1.1.0.40+ {en, de}capsulationKeyCheck test cases test keys of
              incorrect length. The mlkem-native API does not allow passing keys
              of incorrect length. We, hence, fail during decoding instead.
            */
            printf("testPassed=0\n");
            return 0;
          }
          argc--, argv++;

          /* Call function under test */
          acvp_mlkem_encapDecp_VAL_decapsulationKeyCheck(dk);
          break;
        }
#endif /* !MLK_CONFIG_NO_DECAPS_API */
        default:
          goto usage;
      }
      break;
    }
#if !defined(MLK_CONFIG_NO_KEYPAIR_API)
    case keyGen:
    {
      unsigned char z[MLKEM_SYMBYTES];
      unsigned char d[MLKEM_SYMBYTES];
      /* keyGen only for "AFT" */
      if (type != AFT)
      {
        goto keygen_usage;
      }

      /* Parse z */
      if (argc == 0 || decode_hex("z", z, sizeof(z), *argv) != 0)
      {
        goto keygen_usage;
      }
      argc--, argv++;

      /* Parse d */
      if (argc == 0 || decode_hex("d", d, sizeof(d), *argv) != 0)
      {
        goto keygen_usage;
      }
      argc--, argv++;

      /* Call function under test */
      acvp_mlkem_keyGen_AFT(z, d);
      break;
    }
#endif /* !MLK_CONFIG_NO_KEYPAIR_API */
    default:
      goto usage;
  }

  ((void)type);

  return (0);

usage:
  fprintf(stderr, USAGE "\n");
  return (1);

#if !defined(MLK_CONFIG_NO_ENCAPS_API)
encaps_usage:
  fprintf(stderr, ENCAPS_USAGE "\n");
  return (1);

encapsulationKeyCheck_usage:
  fprintf(stderr, ENCAPS_KEY_CHECK_USAGE "\n");
  return (1);
#endif /* !MLK_CONFIG_NO_ENCAPS_API */

#if !defined(MLK_CONFIG_NO_DECAPS_API)
decaps_usage:
  fprintf(stderr, DECAPS_USAGE "\n");
  return (1);

decapsulationKeyCheck_usage:
  fprintf(stderr, DECAPS_KEY_CHECK_USAGE "\n");
  return (1);
#endif /* !MLK_CONFIG_NO_DECAPS_API */

#if !defined(MLK_CONFIG_NO_KEYPAIR_API)
keygen_usage:
  fprintf(stderr, KEYGEN_USAGE "\n");
  return (1);
#endif
}
