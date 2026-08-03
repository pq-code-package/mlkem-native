[//]: # (SPDX-License-Identifier: CC-BY-4.0)

# API conventions

This document describes conventions shared by all public functions declared in [`mlkem/mlkem_native.h`](mlkem/mlkem_native.h). The per-function documentation in that header takes precedence wherever it is more specific.

## Return values

Functions returning `int` return `0` on success and a negative error code on failure. Error codes are enumerated as `MLK_ERR_XXX` constants in `mlkem_native.h`.

Errors have different origins, and not all are fatal. `MLK_ERR_FAIL` reported by the key checks signals malformed key material, which is an expected outcome for untrusted input: the modulus check rejecting a public key, or the public key hash check rejecting a private key. Other errors, such as `MLK_ERR_OUT_OF_MEMORY` or `MLK_ERR_RNG_FAIL`, as well as `MLK_ERR_FAIL` reported by key generation after a failed pairwise consistency test, should never be observed in normal operation and hint at a deeper failure in the system.

An invalid ciphertext is not an error. ML-KEM decapsulation uses implicit rejection, so decapsulating a malformed ciphertext succeeds and yields a pseudorandom shared secret.

Return values must always be checked; the public API is annotated with `warn_unused_result` on compilers that support it.

## Pointer arguments

All pointers are assumed to be valid and non-NULL, and every buffer is assumed to have the size implied by its parameter type. mlkem-native does not conduct pointer validity checks such as NULL comparisons; passing a NULL or otherwise invalid pointer, or an undersized buffer, is undefined behavior. Ensuring these preconditions is the caller's responsibility.

Every buffer in the ML-KEM API has a fixed size determined by the parameter set. There are no pointer/length pairs, and therefore no empty buffers for which a NULL pointer would be admissible.

## Output buffers on error

When a function returns an error, each caller-owned output buffer is left either unchanged or fully zeroized. An output buffer is never left holding partially computed or otherwise stale data that could be mistaken for a valid result.
