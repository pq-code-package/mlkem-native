/* Copyright (c) The mlkem-native project authors */
/* SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT */

/* Init7 section - set up argc/argv registers for main() */
.section .init7,"ax",@progbits

/* AVR calling convention for main(int argc, char** argv):
 * - argc (int, 16-bit) goes in r24:r25 (r24=low, r25=high)
 * - argv (char**, 16-bit pointer) goes in r22:r23 (r22=low, r23=high)
 *
 * The argc/argv block was copied to mlk_argv_base by setup_args (init6):
 * argc at mlk_argv_base, argv array at mlk_argv_base + 2.
 */

lds r30, mlk_argv_base
lds r31, mlk_argv_base+1
ld  r24, Z
ldi r25, 0

movw r22, r30
subi r22, lo8(-2)
sbci r23, hi8(-2)

/* Fall through to init8 - no ret instruction */
