// SPDX-License-Identifier: Apache-2.0
#include "verify.h"
#include <stddef.h>
#include <stdint.h>

/*************************************************
 * Name:        verify
 *
 * Description: Compare two arrays for equality in constant time.
 *
 * Arguments:   const uint8_t *a: pointer to first byte array
 *              const uint8_t *b: pointer to second byte array
 *              size_t len:       length of the byte arrays
 *
 * Returns 0 if the byte arrays are equal, 1 otherwise
 **************************************************/
int verify(const uint8_t *a, const uint8_t *b, size_t len) {
  size_t i;
  uint8_t r = 0;

  for (i = 0; i < len; i++) {
    r |= a[i] ^ b[i];
  }

  return (-(uint64_t)r) >> 63;
}

/*************************************************
 * Name:        cmov
 *
 * Description: Copy len bytes from x to r if b is 1;
 *              don't modify x if b is 0. Requires b to be in {0,1};
 *              assumes two's complement representation of negative integers.
 *              Runs in constant time.
 *
 * Arguments:   uint8_t *r:       pointer to output byte array
 *              const uint8_t *x: pointer to input byte array
 *              size_t len:       Amount of bytes to be copied
 *              uint8_t b:        Condition bit; has to be in {0,1}
 **************************************************/
void cmov(uint8_t *r, const uint8_t *x, size_t len, uint8_t b) {
  size_t i;

  b = -b;
  for (i = 0; i < len; i++) {
    r[i] ^= b & (r[i] ^ x[i]);
  }
}

/*************************************************
 * Note:
 *
 * Constant-time implementation. Relies on basic
 * properties of bitwise ^ or and &.
 **************************************************/
void cmov_int16(int16_t *r, const int16_t v, const uint16_t b) {
// CBMC issues false alarms here for the implicit conversions between
// uint16_t and int, so disable "conversion-check" here for now.
#pragma CPROVER check push
#pragma CPROVER check disable "conversion"

  // b == 0 => mask = 0x0000
  // b == 1 => mask = 0xFFFF
  const uint16_t mask = -b;

  // mask == 0x0000 => *r == (*r ^ 0x0000) == *r
  // mask == 0xFFFF => *r == (*r ^ (*r ^ v)) == (*r ^ *r) ^ v == 0 ^ v == v
  *r ^= mask & ((*r) ^ v);
#pragma CPROVER check pop
}
