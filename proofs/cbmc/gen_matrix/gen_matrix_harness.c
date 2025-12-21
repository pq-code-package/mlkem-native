// Copyright (c) The mlkem-native project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT-0

#include <stdint.h>
#include "indcpa.h"

void harness(void)
{
  {
    /* Dummy use of malloc/free to work around
     * https://github.com/diffblue/cbmc/issues/8814 */
    uint8_t *ptr = malloc(1);
    free(ptr);
  }

  mlk_polymat *a;
  uint8_t *seed;
  int transposed;
  mlk_gen_matrix(a, seed, transposed);
}
