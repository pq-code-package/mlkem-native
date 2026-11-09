/*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */

/* References
 * ==========
 *
 * - [RVPSABI]
 *   RISC-V ABIs Specification
 *   RISC-V International
 *   https://github.com/riscv-non-isa/riscv-elf-psabi-doc
 */

#include <stdio.h>

#include "../../notrandombytes/notrandombytes.h"
#include "abicheck_riscv64.h"

#if defined(MLK_SYS_RISCV64)

/* Callee-saved set per @[RVPSABI, Section "Integer Register Convention"] and
 * @[RVPSABI, Section "Floating-point Register Convention"]. All vector
 * registers and vector CSRs are caller-saved. */
int check_riscv64_lp64d_compliance(struct riscv64_register_state *before,
                                   struct riscv64_register_state *after,
                                   int quiet)
{
  int violations = 0;
  int i;

  /* gp (x3) and tp (x4) are reserved for the platform. The call stub does
   * not seed them, but kernels must leave them unchanged. */
  if (before->gpr[3] != after->gpr[3])
  {
    MLK_ABI_VIOLATION(quiet, "%s modified\n", "gp");
    violations++;
  }
  if (before->gpr[4] != after->gpr[4])
  {
    MLK_ABI_VIOLATION(quiet, "%s modified\n", "tp");
    violations++;
  }

  /* s0-s1 (x8-x9) and s2-s11 (x18-x27). */
  for (i = 0; i < 32; i++)
  {
    if ((i == 8 || i == 9 || (i >= 18 && i <= 27)) &&
        before->gpr[i] != after->gpr[i])
    {
      MLK_ABI_VIOLATION(quiet, "x%d modified\n", i);
      violations++;
    }
  }

#if defined(__riscv_float_abi_double)
  /* fs0-fs1 (f8-f9) and fs2-fs11 (f18-f27). */
  for (i = 0; i < 32; i++)
  {
    if ((i == 8 || i == 9 || (i >= 18 && i <= 27)) &&
        before->fpr[i] != after->fpr[i])
    {
      MLK_ABI_VIOLATION(quiet, "f%d modified\n", i);
      violations++;
    }
  }
#endif /* __riscv_float_abi_double */

  return violations;
}

void init_riscv64_register_state(struct riscv64_register_state *state)
{
  randombytes((uint8_t *)state, sizeof(*state));
}

#endif /* MLK_SYS_RISCV64 */
