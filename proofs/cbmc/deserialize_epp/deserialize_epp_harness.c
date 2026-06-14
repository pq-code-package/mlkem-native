// Copyright (c) The mlkem-native project authors
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

#include <kem.h>
#include <poly.h>

#define mlk_deserialize_epp MLK_NAMESPACE(deserialize_epp)
void mlk_deserialize_epp(mlk_poly *p, const uint8_t in[MLKEM_EPP_BYTES]);

void harness(void)
{
  {
    /* Dummy use of `free` to work around CBMC issue #8814. */
    free(NULL);
  }

  uint8_t *in;
  mlk_poly *p;

  mlk_deserialize_epp(p, in);
}
