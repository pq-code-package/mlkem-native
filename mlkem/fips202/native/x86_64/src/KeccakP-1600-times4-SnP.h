/*
 * Copyright (c) 2024 The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0
 */

/*
Implementation by the Keccak, Keyak and Ketje Teams, namely, Guido Bertoni,
Joan Daemen, Michaël Peeters, Gilles Van Assche and Ronny Van Keer, hereby
denoted as "the implementer".

For more information, feedback or questions, please refer to our websites:
http://keccak.noekeon.org/
http://keyak.noekeon.org/
http://ketje.noekeon.org/

To the extent possible under law, the implementer has waived all copyright
and related or neighboring rights to the source code in this file.
http://creativecommons.org/publicdomain/zero/1.0/
*/

#ifndef KECCAKP_1600_TIMES4_SNP_H
#define KECCAKP_1600_TIMES4_SNP_H

/** For the documentation, see PlSnP-documentation.h.
 */

#include <stddef.h>
#include "../../../../common.h"
#include "KeccakP-SIMD256-config.h"

#define KeccakP1600times4_PermuteAll_24rounds \
  FIPS202_NAMESPACE(KeccakP1600times4_PermuteAll_24rounds)
void KeccakP1600times4_PermuteAll_24rounds(void *states);

#endif /* KECCAKP_1600_TIMES4_SNP_H */
