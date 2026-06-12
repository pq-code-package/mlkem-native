/*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */

#ifndef MLK_TEST_ABICHECK_ABICHECK_COMMON_H
#define MLK_TEST_ABICHECK_ABICHECK_COMMON_H

#include <stdint.h>

/*
 * Resolve the build config and sys.h. Defines MLK_BUILD_INTERNAL (so
 * MLK_CONFIG_FILE's MLK_CONFIG_CUSTOM_CAPABILITY_FUNC body, gated on it, is
 * visible) and pulls in the resolved config + sys.h. We don't include
 * common.h: it would drag in backend constant tables that older compilers do
 * not drop, forcing them into the abicheck link.
 *
 * Paths use the project's -Imlkem search path (set in test/mk/components.mk)
 * so this header is includable from any depth under test/abicheck/.
 */
#define MLK_BUILD_INTERNAL
#if defined(MLK_CONFIG_FILE)
#include MLK_CONFIG_FILE
#else
#include "mlkem_native_config.h"
#endif
#include "src/sys.h"

/* Return codes for check_<kernel>(), shared with abicheck.c. */
#define MLK_ABICHECK_PASSED 0  /* No violation in any iteration. */
#define MLK_ABICHECK_SKIPPED 1 /* Host lacks the required ISA capability. */
#define MLK_ABICHECK_FAILED                        \
  (-1) /* Violation observed, or arch unsupported. \
        */

/* Randomized trials per kernel; each trial reseeds the register state and
 * pointer-arg buffers. */
#define MLK_ABICHECK_NUM_TESTS 100

/* Quiet suppresses the per-violation diagnostic (used by the selftest, whose
 * corrupters always fire). */
#define MLK_ABICHECK_VERBOSE 0
#define MLK_ABICHECK_QUIET 1

/* If quiet, suppress the per-register diagnostic. Non-variadic to stay
 * C90-clean under -pedantic; fixed names are passed via "%s". */
#define MLK_ABI_VIOLATION(quiet, fmt, arg)           \
  do                                                 \
  {                                                  \
    if (!(quiet))                                    \
    {                                                \
      fprintf(stderr, "ABI violation: " fmt, (arg)); \
    }                                                \
  } while (0)

/* Registry entry shared by all per-arch checks_{arch}_all.h headers and
 * consumed by abicheck.c. */
typedef struct
{
  const char *name;
  int (*check_func)(void);
} abicheck_entry_t;

/* The per-arch register-state struct and its call-stub / compliance / init
 * declarations live in test/abicheck/<arch>/abicheck_<arch>.h, with the
 * compliance/init implementations in the matching abicheck_<arch>.c. The
 * generated check_*.c include their own arch's header; selftest.c, which
 * dispatches across all arches, includes them all directly. The driver
 * abicheck.c needs only the shared definitions above, so it pulls in none. */

#endif /* !MLK_TEST_ABICHECK_ABICHECK_COMMON_H */
