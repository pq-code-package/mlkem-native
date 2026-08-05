/*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */

/*
 * Assertion helpers shared by the mlkem-native test and benchmark drivers.
 *
 * Two flavours are provided:
 *
 * - CHECK(cond) for conditions that are not return codes, e.g. memcmp()
 *   comparisons or the outcome of a test helper. On failure it reports the
 *   source location only, as there is no meaningful value to print.
 *
 * - CHECK_ERR(call, expected) for calls returning an mlkem-native return
 *   code, i.e. the crypto_kem_xxx API. On failure it reports the expected and
 *   the actual code, each numerically and by name, which makes a mismatch
 *   diagnosable from the test log alone -- and greppable from CI scripts.
 *
 * Use CHECK_ERR only where the value really is an MLK_ERR_XXX code, otherwise
 * the reported name is meaningless. Notably it does NOT apply to:
 * randombytes(), which is consumer-provided and returns an unspecified
 * non-zero value on failure; and values that merely aggregate return codes,
 * e.g. a bitwise OR over several calls.
 *
 * Both macros `return 1` from the enclosing function on failure. Drivers
 * whose enclosing functions return void define MLK_TEST_CHECK_EXIT before
 * including this header to terminate the process instead.
 */

#ifndef MLK_TEST_SRC_TEST_COMMON_H
#define MLK_TEST_SRC_TEST_COMMON_H

#include <stdio.h>

#if defined(MLK_TEST_CHECK_EXIT)
#include <stdlib.h>
#endif

#include "../../mlkem/src/common.h"

/*
 * Name of an mlkem-native return code, for diagnostics.
 *
 * MLK_INLINE also silences unused-function warnings in drivers that use only
 * CHECK(), so no separate gating on the used assertion flavour is needed.
 */
static MLK_INLINE const char *mlk_err_name(int rc)
{
  switch (rc)
  {
    case 0:
      return "Success";
    case MLK_ERR_FAIL:
      return "MLK_ERR_FAIL";
    case MLK_ERR_OUT_OF_MEMORY:
      return "MLK_ERR_OUT_OF_MEMORY";
    case MLK_ERR_RNG_FAIL:
      return "MLK_ERR_RNG_FAIL";
    case MLK_ERR_INVALID_PK:
      return "MLK_ERR_INVALID_PK";
    case MLK_ERR_INVALID_SK:
      return "MLK_ERR_INVALID_SK";
    case MLK_ERR_PCT_FAIL:
      return "MLK_ERR_PCT_FAIL";
    default:
      return "unknown error";
  }
}

#if defined(MLK_TEST_CHECK_EXIT)
#define MLK_TEST_FAIL() exit(1)
#else
#define MLK_TEST_FAIL() return 1
#endif

/* Assert a condition that is not a return code, e.g. a memcmp() comparison. */
#define CHECK(x)                                              \
  do                                                          \
  {                                                           \
    int rc;                                                   \
    rc = (x);                                                 \
    if (!rc)                                                  \
    {                                                         \
      fprintf(stderr, "ERROR (%s,%d)\n", __FILE__, __LINE__); \
      MLK_TEST_FAIL();                                        \
    }                                                         \
  } while (0)

/*
 * Assert that `call` returns exactly `expected`. `call` is evaluated once.
 *
 * On mismatch, both codes are printed numerically and by name, e.g.
 *
 *   ERROR (test/src/test_mlkem.c,94): Expected -4 (MLK_ERR_INVALID_PK) for
 *   crypto_kem_enc(ct, key_b, pk), but got 0 (Success)
 */
#define CHECK_ERR(call, expected)                                          \
  do                                                                       \
  {                                                                        \
    const int mlk_got = (call);                                            \
    const int mlk_exp = (expected);                                        \
    if (mlk_got != mlk_exp)                                                \
    {                                                                      \
      fprintf(stderr,                                                      \
              "ERROR (%s,%d): Expected %d (%s) for %s, but got %d (%s)\n", \
              __FILE__, __LINE__, mlk_exp, mlk_err_name(mlk_exp), #call,   \
              mlk_got, mlk_err_name(mlk_got));                             \
      MLK_TEST_FAIL();                                                     \
    }                                                                      \
  } while (0)

#endif /* !MLK_TEST_SRC_TEST_COMMON_H */
