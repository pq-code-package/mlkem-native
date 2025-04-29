/*
 * Copyright (c) 2024-2025 The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0
 */

/* References
 * ==========
 *
 * - [pqcarchive]
 *   NIST PQC Archive
 *   National Institute of Standards and Technology
 *   https://csrc.nist.gov/Projects/post-quantum-cryptography/pqc-archive
 */

/* Derived from [@pqcarchive, Source Code Files for KATs] provided by NIST
 * under the following terms of use:
 *
 *
 * NIST-developed software is provided by NIST as a public service. You may
 * use, copy, and distribute copies of the software in any medium, provided
 * that you keep intact this entire notice. You may improve, modify, and
 * create derivative works of the software or any portion of the software, and
 * you may copy and distribute such modifications or works. Modified works
 * should carry a notice stating that you changed the software and should note
 * the date and nature of any such change. Please explicitly acknowledge the
 * National Institute of Standards and Technology as the source of the
 * software.
 *
 * NIST-developed software is expressly provided "AS IS." NIST MAKES NO
 * WARRANTY OF ANY KIND, EXPRESS, IMPLIED, IN FACT, OR ARISING BY OPERATION OF
 * LAW, INCLUDING, WITHOUT LIMITATION, THE IMPLIED WARRANTY OF
 * MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE, NON-INFRINGEMENT, AND
 * DATA ACCURACY. NIST NEITHER REPRESENTS NOR WARRANTS THAT THE OPERATION OF
 * THE SOFTWARE WILL BE UNINTERRUPTED OR ERROR-FREE, OR THAT ANY DEFECTS WILL
 * BE CORRECTED. NIST DOES NOT WARRANT OR MAKE ANY REPRESENTATIONS REGARDING
 * THE USE OF THE SOFTWARE OR THE RESULTS THEREOF, INCLUDING BUT NOT LIMITED
 * TO THE CORRECTNESS, ACCURACY, RELIABILITY, OR USEFULNESS OF THE SOFTWARE.
 *
 * You are solely responsible for determining the appropriateness of using and
 * distributing the software and you assume all risks associated with its use,
 * including but not limited to the risks and costs of program errors,
 * compliance with applicable laws, damage to or loss of data, programs or
 * equipment, and the unavailability or interruption of operation. This
 * software is not intended to be used in any situation where a failure could
 * cause risk of injury or damage to property. The software developed by NIST
 * employees is not subject to copyright protection within the United
 * States.
 */

#include <assert.h>
#include <stdint.h>
#include <string.h>

#include "aes.h"
#include "nistrng.h"

typedef struct
{
  unsigned char key[AES256_KEYBYTES];
  unsigned char ctr[AES_BLOCKBYTES];
} nistkatctx;

static nistkatctx ctx;

static void _aes256_ecb(unsigned char key[AES256_KEYBYTES],
                        unsigned char ctr[AES_BLOCKBYTES],
                        unsigned char buffer[AES_BLOCKBYTES])
{
  aes256ctx aesctx;
  aes256_ecb_keyexp(&aesctx, key);
  aes256_ecb(buffer, ctr, 1, &aesctx);
  aes256_ctx_release(&aesctx);
}

static void aes256_block_update(uint8_t block[AES_BLOCKBYTES])
{
  int j;
  for (j = AES_BLOCKBYTES - 1; j >= 0; j--)
  {
    ctx.ctr[j]++;

    if (ctx.ctr[j] != 0x00)
    {
      break;
    }
  }

  _aes256_ecb(ctx.key, ctx.ctr, block);
}

static void nistkat_update(const unsigned char *provided_data,
                           unsigned char *key, unsigned char *ctr)
{
  int i;
  int len = AES256_KEYBYTES + AES_BLOCKBYTES;
  uint8_t tmp[AES256_KEYBYTES + AES_BLOCKBYTES];

  for (i = 0; i < len / AES_BLOCKBYTES; i++)
  {
    aes256_block_update(tmp + AES_BLOCKBYTES * i);
  }

  if (provided_data)
  {
    for (i = 0; i < len; i++)
    {
      tmp[i] ^= provided_data[i];
    }
  }

  memcpy(key, tmp, AES256_KEYBYTES);
  memcpy(ctr, tmp + AES256_KEYBYTES, AES_BLOCKBYTES);
}

void nist_kat_init(
    unsigned char entropy_input[AES256_KEYBYTES + AES_BLOCKBYTES],
    const unsigned char
        personalization_string[AES256_KEYBYTES + AES_BLOCKBYTES],
    int security_strength)
{
  int i;
  int len = AES256_KEYBYTES + AES_BLOCKBYTES;
  uint8_t seed_material[AES256_KEYBYTES + AES_BLOCKBYTES];
  (void)security_strength;

  memcpy(seed_material, entropy_input, len);
  if (personalization_string)
  {
    for (i = 0; i < len; i++)
    {
      seed_material[i] ^= personalization_string[i];
    }
  }
  memset(ctx.key, 0x00, AES256_KEYBYTES);
  memset(ctx.ctr, 0x00, AES_BLOCKBYTES);
  nistkat_update(seed_material, ctx.key, ctx.ctr);
}

void randombytes(uint8_t *buf, size_t n)
{
  size_t i;
  uint8_t block[AES_BLOCKBYTES];

  size_t nb = n / AES_BLOCKBYTES;
  size_t tail = n % AES_BLOCKBYTES;

  for (i = 0; i < nb; i++)
  {
    aes256_block_update(block);
    memcpy(buf + i * AES_BLOCKBYTES, block, AES_BLOCKBYTES);
  }

  if (tail > 0)
  {
    aes256_block_update(block);
    memcpy(buf + nb * AES_BLOCKBYTES, block, tail);
  }

  nistkat_update(NULL, ctx.key, ctx.ctr);
}
