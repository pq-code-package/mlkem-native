// Copyright (c) The mlkem-native project authors
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

#include <kem.h>
#include <poly_k.h>

#define mlk_serialize_polyvec_16le MLK_NAMESPACE(serialize_polyvec_16le)
void mlk_serialize_polyvec_16le(uint8_t out[MLKEM_POLYVEC16_BYTES],
                                const mlk_polyvec *v);

void harness(void)
{
  {
    /* Dummy use of `free` to work around CBMC issue #8814. */
    free(NULL);
  }

  uint8_t *out;
  mlk_polyvec *v;

  mlk_serialize_polyvec_16le(out, v);
}
