/* Copyright (c) The mlkem-native project authors */
/* SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT */

/* Init7 section - set up argc/argv registers for main() */
.section .init7,"ax",@progbits

/* AVR calling convention for main(int argc, char** argv):
 * - argc (int, 16-bit) goes in r24:r25 (r24=low, r25=high)
 * - argv (char**, 16-bit pointer) goes in r22:r23 (r22=low, r23=high)
 */

/* Load argc from 0x2000 */
ldi r30, 0x00
ldi r31, 0x20
ld  r24, Z
ldi r25, 0

/* Set argv = 0x2002 */
ldi r22, lo8(0x2002)
ldi r23, hi8(0x2002)

/* Fall through to init8 - no ret instruction */
