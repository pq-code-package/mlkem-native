// Copyright (c) The mlkem-native project authors
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

#include <kem.h>
#include <poly.h>

#define mlk_serialize_epp MLK_NAMESPACE(serialize_epp)
void mlk_serialize_epp(uint8_t out[MLKEM_EPP_BYTES], const mlk_poly *p);

void harness(void)
{
  {
    /* Dummy use of `free` to work around CBMC issue #8814. */
    free(NULL);
  }

  uint8_t *out;
  mlk_poly *p;

  mlk_serialize_epp(out, p);
}
