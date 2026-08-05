/*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */
#ifndef MLK_TEST_DECODE_HEX_H
#define MLK_TEST_DECODE_HEX_H

#include <stddef.h>
#include <stdio.h>
#include <string.h>

/* Decode hex character [0-9A-Fa-f] into 0-15. Returns 0xFF for any other
 * character: a valid nibble is 0-15, so 0xFF is an out-of-band value that never
 * collides with a real digit and thus serves as the "not hex" sentinel. */
static unsigned char decode_hex_char(char hex)
{
  if (hex >= '0' && hex <= '9')
  {
    return (unsigned char)(hex - '0');
  }
  else if (hex >= 'A' && hex <= 'F')
  {
    return (unsigned char)(10 + (unsigned char)(hex - 'A'));
  }
  else if (hex >= 'a' && hex <= 'f')
  {
    return (unsigned char)(10 + (unsigned char)(hex - 'a'));
  }
  else
  {
    return 0xFF;
  }
}

/* Decode the value of a `prefix=HEX` argument in place, overwriting the
 * hex encoding with the raw bytes. Returns a pointer to the decoded bytes
 * inside the argument string, or NULL on parse failure. */
static unsigned char *decode_hex(const char *prefix, size_t out_len, char *hex)
{
  size_t i;
  const char *arg = hex;
  size_t hex_len = strlen(hex);
  size_t prefix_len = strlen(prefix);
  unsigned char *out;

  /*
   * Check that hex starts with `prefix=`
   * Use memcmp, not strcmp
   */
  if (hex_len < prefix_len + 1 || memcmp(prefix, hex, prefix_len) != 0 ||
      hex[prefix_len] != '=')
  {
    goto hex_usage;
  }

  hex += prefix_len + 1;
  hex_len -= prefix_len + 1;

  if (hex_len != 2 * out_len)
  {
    goto hex_usage;
  }

  out = (unsigned char *)hex;
  for (i = 0; i < out_len; i++)
  {
    unsigned hex0 = decode_hex_char(hex[2 * i]);
    unsigned hex1 = decode_hex_char(hex[2 * i + 1]);
    if (hex0 == 0xFF || hex1 == 0xFF)
    {
      goto hex_usage;
    }

    out[i] = (unsigned char)((hex0 << 4) | hex1);
  }

  return out;

hex_usage:
  fprintf(stderr,
          "Argument %s invalid: Expected argument of the form '%s=HEX' with "
          "HEX being a hex encoding of %u bytes\n",
          arg, prefix, (unsigned)out_len);
  return NULL;
}

#endif /* !MLK_TEST_DECODE_HEX_H */
