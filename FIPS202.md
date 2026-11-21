[//]: # (SPDX-License-Identifier: CC-BY-4.0)

# Replacing FIPS-202

If your library has a FIPS-202[^FIPS202] implementation, you can use it instead of the one shipped with mlkem-native.

1. Replace `mlkem/src/fips202/*` by your own FIPS-202 implementation.
2. Provide replacements for the headers [`mlkem/src/fips202/fips202.h`](mlkem/src/fips202/fips202.h) and [`mlkem/src/fips202/fips202x4.h`](mlkem/src/fips202/fips202x4.h) and the
functionalities specified therein:
  * Structure definitions for `mlk_shake128ctx` and `mlk_shake128x4ctx`
  * `mlk_shake128_init()`: Initialize a SHAKE-128 context
  * `mlk_shake128_absorb_once()`: Perform a single absorb step on a SHAKE-128 context
  * `mlk_shake128_squeezeblocks()`: Squeeze SHAKE-128 context
  * `mlk_shake128_release()`: Release a SHAKE-128 context after use
  * `mlk_shake256()`, `mlk_sha3_256()`, `mlk_sha3_512()`: One-shot SHAKE-256 / SHA3-256 / SHA3-512 operations
  * `mlk_shake256x4()`: One-shot 4x-batched SHAKE-256 operation
  * `mlk_shake128x4_init()`: Initialize a 4x-batched SHAKE-128 context
  * `mlk_shake128x4_absorb_once()`: Perform a single absorb step on a 4x-batched SHAKE-128 context
  * `mlk_shake128x4_squeezeblocks()`: Squeeze 4x-batched SHAKE-128 context
  * `mlk_shake128x4_release()`: Release a 4x-batched SHAKE-128 context after use

See [`mlkem/src/fips202/fips202.h`](mlkem/src/fips202/fips202.h) and [`mlkem/src/fips202/fips202x4.h`](mlkem/src/fips202/fips202x4.h) for more details. Note that the structure
definitions may differ from those shipped with mlkem-native: In particular, you may fall back to an incremental hashing
implementation which tracks the current offset in its state.

## Implementations that can fail

By default, the functions of a custom FIPS-202 implementation return `void` and cannot fail. If your implementation can
fail, set `MLK_CONFIG_FIPS202_CAN_FAIL`. All functions listed above,
including `*_init()` and `*_release()`, must then return an `int`: 0 on success, and any non-zero value on failure.
mlkem-native checks every call. If one fails, the public API function returns `MLK_ERR_FIPS202_FAIL`, and its
output buffers are left unmodified or zeroized. Whether a call fails must not depend on the contents
of its input and output buffers or of the FIPS-202 state, as these can be secret. It may depend on the lengths of
the inputs and outputs, which are public.

The FIPS-202 implementation shipped with mlkem-native never fails. In the next major version (v3), custom
implementations are planned to always return `int`, and `MLK_CONFIG_FIPS202_CAN_FAIL` will be removed.

## Example

See [`examples/bring_your_own_fips202/`](examples/bring_your_own_fips202/) for an example how to use a custom FIPS-202
implementation.

<!--- bibliography --->
[^FIPS202]: National Institute of Standards and Technology: FIPS202 SHA-3 Standard: Permutation-Based Hash and Extendable-Output Functions, [https://csrc.nist.gov/pubs/fips/202/final](https://csrc.nist.gov/pubs/fips/202/final)
