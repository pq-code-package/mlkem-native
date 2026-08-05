/*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "../../mlkem/src/common.h"
#include "../src/decode_hex.h"

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

#if !defined(MLK_CONFIG_NO_DECAPS_API)
#if !defined(MLK_CONFIG_NO_KEYPAIR_API)
/* Decapsulation key expanded from a seed. Kept in .bss (not on main's stack)
 * so that main's per-case argument handling stays small on RAM-tight targets.
 */
static unsigned char acvp_expanded_dk[MLKEM_SK_BYTES];
#endif /* !MLK_CONFIG_NO_KEYPAIR_API */

/*
 * Resolve the decapsulation-key argument. "dk=HEX" (keyFormat 'expanded') is
 * decoded in place and a pointer into arg is returned; "seed=HEX" (keyFormat
 * 'seed') is a seed d||z expanded via keyGen. Returns NULL on failure.
 * MLK_NOINLINE keeps the keyGen scratch (ek) out of the caller's (main's)
 * stack frame; under -fsanitize=undefined it would not share slots and would
 * overflow AVR RAM.
 */
static MLK_NOINLINE unsigned char *decode_dk(char *arg)
{
  size_t seed_len = strlen("seed=");

  /* Prefix check via memcmp; strncmp is unavailable on baremetal builds. */
  if (strlen(arg) >= seed_len && memcmp(arg, "seed=", seed_len) == 0)
  {
#if !defined(MLK_CONFIG_NO_KEYPAIR_API)
    /* TODO(#1841): ek is scratch that is never used. Avoiding it needs a
     * keyGen entry point deriving only dk from the seed. */
    unsigned char ek[MLKEM_PK_BYTES];
    unsigned char *coins = decode_hex("seed", 2 * MLKEM_SYMBYTES, arg);
    if (coins == NULL)
    {
      return NULL;
    }
    if (mlk_kem_keypair_derand(ek, acvp_expanded_dk, coins) != 0)
    {
      fprintf(stderr, "Failed to expand seed into decapsulation key\n");
      return NULL;
    }
    return acvp_expanded_dk;
#else  /* !MLK_CONFIG_NO_KEYPAIR_API */
    fprintf(stderr, "seed key format requires the keyGen API\n");
    return NULL;
#endif /* MLK_CONFIG_NO_KEYPAIR_API */
  }
  return decode_hex("dk", MLKEM_SK_BYTES, arg);
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
          unsigned char *ek, *m;
          /* Encapsulation only for "AFT" */
          if (type != AFT)
          {
            goto encaps_usage;
          }

          /* Parse ek */
          if (argc == 0 ||
              (ek = decode_hex("ek", MLKEM_PK_BYTES, *argv)) == NULL)
          {
            goto encaps_usage;
          }
          argc--, argv++;

          /* Parse m */
          if (argc == 0 || (m = decode_hex("m", MLKEM_SYMBYTES, *argv)) == NULL)
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
          unsigned char *dk, *c;
          /* Decapsulation only for "VAL" */
          if (type != VAL)
          {
            goto decaps_usage;
          }

          /* Parse dk (expanded key, or a seed to expand) */
          if (argc == 0 || (dk = decode_dk(*argv)) == NULL)
          {
            goto decaps_usage;
          }
          argc--, argv++;

          /* Parse c */
          if (argc == 0 || (c = decode_hex("c", MLKEM_CT_BYTES, *argv)) == NULL)
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
          unsigned char *ek;
          /* encapsulationKeyCheck only for "VAL" */
          if (type != VAL || argc == 0)
          {
            goto encapsulationKeyCheck_usage;
          }

          /* Parse ek */
          if ((ek = decode_hex("ek", MLKEM_PK_BYTES, *argv)) == NULL)
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
          unsigned char *dk;
          /* Encapsulation only for "VAL" */
          if (type != VAL || argc == 0)
          {
            goto decapsulationKeyCheck_usage;
          }

          /* Parse dk */
          if ((dk = decode_hex("dk", MLKEM_SK_BYTES, *argv)) == NULL)
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
      unsigned char *z, *d;
      /* keyGen only for "AFT" */
      if (type != AFT)
      {
        goto keygen_usage;
      }

      /* Parse z */
      if (argc == 0 || (z = decode_hex("z", MLKEM_SYMBYTES, *argv)) == NULL)
      {
        goto keygen_usage;
      }
      argc--, argv++;

      /* Parse d */
      if (argc == 0 || (d = decode_hex("d", MLKEM_SYMBYTES, *argv)) == NULL)
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
