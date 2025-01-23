/*
 * Copyright (c) 2024 The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0
 */

/*
 * FIPS-202 native interface
 *
 * This header is primarily for documentation purposes.
 * It should not be included by backend implementations.
 */
#ifdef MLKEM_NATIVE_FIPS202_NATIVE_API_H
#error \
    "The FIPS-202 backend API `mlkem/fips202/native/api.h` "		\
    "should not be directly included. Please include the relevant "	\
    "structure headers directly."
#else /* MLKEM_NATIVE_FIPS202_NATIVE_API_H */
#define MLKEM_NATIVE_FIPS202_NATIVE_API_H

#include <stdint.h>

/*
 * This is the C<->native interface allowing for the drop-in
 * of custom Keccak-F1600 implementations.
 *
 * A _backend_ is a specific implementation of parts of this interface.
 *
 * You can replace 1-fold, 2-fold, or 4-fold batched Keccak-F1600.
 * To enable, set MLKEM_USE_FIPS202_X{1,2,4}_NATIVE in your backend,
 * and define the inline wrapper keccak_f1600_x{1,2,4}_native() to
 * forward to your implementation.
 */

#if defined(MLKEM_USE_FIPS202_X1_NATIVE)
static INLINE void keccak_f1600_x1_native(uint64_t *state)
__contract__(
  requires(memory_no_alias(state, sizeof(uint64_t) * 25 * 1))
  assigns(memory_slice(state, sizeof(uint64_t) * 25 * 1)));
#endif
#if defined(MLKEM_USE_FIPS202_X2_NATIVE)
static INLINE void keccak_f1600_x2_native(uint64_t *state)
__contract__(
  requires(memory_no_alias(state, sizeof(uint64_t) * 25 * 2))
  assigns(memory_slice(state, sizeof(uint64_t) * 25 * 2)));
#endif
#if defined(MLKEM_USE_FIPS202_X4_NATIVE)
static INLINE void keccak_f1600_x4_native(uint64_t *state)
__contract__(
  requires(memory_no_alias(state, sizeof(uint64_t) * 25 * 4))
  assigns(memory_slice(state, sizeof(uint64_t) * 25 * 4)));
#endif

#endif /* MLKEM_NATIVE_FIPS202_NATIVE_API_H */
