/*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */

#ifndef MLK_FIPS202_NATIVE_API_H
#define MLK_FIPS202_NATIVE_API_H
/*
 * FIPS-202 native interface
 *
 * This header is primarily for documentation purposes.
 * It should not be included by backend implementations.
 */

#include <stdint.h>
#include "../../cbmc.h"

/*
 * This is the C<->native interface allowing for the drop-in
 * of custom Keccak-F1600 implementations.
 *
 * A _backend_ is a specific implementation of parts of this interface.
 *
 * You can replace 1-fold, 2-fold, or 4-fold batched Keccak-F1600.
 * To enable, set MLK_USE_FIPS202_X1_NATIVE etc. in your backend,
 * and define the inline wrapper keccak_f1600_x1_native() etc. to
 * forward to your implementation.
 */

#if defined(MLK_USE_FIPS202_X1_NATIVE)
static MLK_INLINE void mlk_keccak_f1600_x1_native(uint64_t *state)
__contract__(
  requires(memory_no_alias(state, sizeof(uint64_t) * 25 * 1))
  assigns(memory_slice(state, sizeof(uint64_t) * 25 * 1)));
#endif /* MLK_USE_FIPS202_X1_NATIVE */
#if defined(MLK_USE_FIPS202_X2_NATIVE)
static MLK_INLINE void mlk_keccak_f1600_x2_native(uint64_t *state)
__contract__(
  requires(memory_no_alias(state, sizeof(uint64_t) * 25 * 2))
  assigns(memory_slice(state, sizeof(uint64_t) * 25 * 2)));
#endif /* MLK_USE_FIPS202_X2_NATIVE */
#if defined(MLK_USE_FIPS202_X4_NATIVE)
static MLK_INLINE void mlk_keccak_f1600_x4_native(uint64_t *state)
__contract__(
  requires(memory_no_alias(state, sizeof(uint64_t) * 25 * 4))
  assigns(memory_slice(state, sizeof(uint64_t) * 25 * 4)));
#endif /* MLK_USE_FIPS202_X4_NATIVE */

#endif /* !MLK_FIPS202_NATIVE_API_H */
