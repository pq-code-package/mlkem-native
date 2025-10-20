[//]: # (SPDX-License-Identifier: CC-BY-4.0)

# Custom FIPS-202 with Static State

This directory contains a copy of tiny_sha3 [^tiny_sha3], but wrapped so that is operates on a single global state only.

This illustrates and tests the configuration option `MLK_CONFIG_SERIAL_FIPS202_ONLY` which should be used
when interfacing with an external FIPS202 implementation -- for example, a hardware accelerator -- that has only
a single global state.

<!--- bibliography --->
[^tiny_sha3]: Markku-Juhani O. Saarinen: tiny_sha3, [https://github.com/mjosaarinen/tiny_sha3](https://github.com/mjosaarinen/tiny_sha3)
