// Copyright (c) The mlkem-native project authors
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

#include <kem.h>
#include <poly_k.h>

#define mlk_deserialize_polyvec_16le MLK_NAMESPACE(deserialize_polyvec_16le)
void mlk_deserialize_polyvec_16le(mlk_polyvec *v,
                                  const uint8_t in[MLKEM_POLYVEC16_BYTES]);

void harness(void)
{
  {
    /* Dummy use of `free` to work around CBMC issue #8814. */
    free(NULL);
  }

  uint8_t *in;
  mlk_polyvec *v;

  mlk_deserialize_polyvec_16le(v, in);
}
