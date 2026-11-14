/*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */

/* References
 * ==========
 *
 * - [FIPS203]
 *   FIPS 203 Module-Lattice-Based Key-Encapsulation Mechanism Standard
 *   National Institute of Standards and Technology
 *   https://csrc.nist.gov/pubs/fips/203/final
 */

/*yaml
  Name: poly_frombytes_aarch64_asm
  Description: Convert byte representation to polynomial
  Signature: void mlk_poly_frombytes_aarch64_asm(int16_t r[256], const uint8_t a[384])
  ABI:
    Architecture: aarch64
    CallingConvention: AAPCS64
    Features: [NEON]
    x0:
      type: buffer
      size_bytes: 512
      permissions: write-only
      c_parameter: int16_t r[256]
      description: Output polynomial
    x1:
      type: buffer
      size_bytes: 384
      permissions: read-only
      c_parameter: const uint8_t a[384]
      description: Input byte array
  Stack:
    bytes: 0
*/


/*
 * WARNING: This file is auto-derived from the mlkem-native source file
 *   dev/aarch64_opt/src/mlkem_poly_frombytes_aarch64_asm.S using scripts/simpasm. Do not modify it directly.
 */

.text
.balign 4
#ifdef __APPLE__
.global _mlk_poly_frombytes_aarch64_asm
_mlk_poly_frombytes_aarch64_asm:
#else
.global mlk_poly_frombytes_aarch64_asm
mlk_poly_frombytes_aarch64_asm:
#endif

        .cfi_startproc
        movi v16.16b, #0xf
        mov x2, #0x8                // =8

Lmlk_poly_frombytes_loop_start:
        ld3 { v0.16b, v1.16b, v2.16b }, [x1], #48
        and v3.16b, v1.16b, v16.16b
        zip1 v4.16b, v0.16b, v3.16b
        zip2 v6.16b, v0.16b, v3.16b
        zip1 v5.16b, v1.16b, v2.16b
        zip2 v7.16b, v1.16b, v2.16b
        ushr v5.8h, v5.8h, #0x4
        ushr v7.8h, v7.8h, #0x4
        st2 { v4.8h, v5.8h }, [x0], #32
        st2 { v6.8h, v7.8h }, [x0], #32
        subs x2, x2, #0x1
        cbnz x2, Lmlk_poly_frombytes_loop_start
        ret
        .cfi_endproc

#if defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
