/*
 * Copyright (c) The mldsa-native project authors
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT OR CC0
 */
/*
 * Implementation by the Keccak, Keyak and Ketje Teams, namely, Guido Bertoni,
 * Joan Daemen, Michaël Peeters, Gilles Van Assche and Ronny Van Keer, hereby
 * denoted as "the implementer".
 * Additional optimizations by Alexandre Adomnicai.
 *
 * For more information, feedback or questions, please refer to our websites:
 * http:// keccak.noekeon.org/
 * http:// keyak.noekeon.org/
 * http:// ketje.noekeon.org/
 *
 * To the extent possible under law, the implementer has waived all copyright
 * and related or neighboring rights to the source code in this file.
 * http:// creativecommons.org/publicdomain/zero/1.0/
 *
 * WARNING: These functions work only on little endian CPU with@ ARMv7m architecture (ARM Cortex-M3, ...).
 */

#include "../../../../common.h"
#if defined(MLK_FIPS202_ARMV81M_NEED_X1) && \
    !defined(MLK_CONFIG_MULTILEVEL_NO_SHARED)

 .thumb
 .syntax unified
.text

 @ Credit: Henry S. Warren, Hacker''s Delight, Addison-Wesley, 2002
.macro	fromBitInterleaving		x0, x1, t

 movs	\t, \x0					@ t = x0@
 bfi		\x0, \x1, #16, #16		@ x0 = (x0 & 0x0000FFFF) | (x1 << 16)@
 bfc		\x1, #0, #16			@	x1 = (t >> 16) | (x1 & 0xFFFF0000)@
 orr		\x1, \x1, \t, LSR #16

    eor		\t, \x0, \x0, LSR #8    @ t = (x0 ^ (x0 >>  8)) & 0x0000FF00UL@  x0 = x0 ^ t ^ (t <<  8)@
 and		\t, #0x0000FF00
    eors	\x0, \x0, \t
    eor		\x0, \x0, \t, LSL #8

    eor		\t, \x0, \x0, LSR #4	@ t = (x0 ^ (x0 >>  4)) & 0x00F000F0UL@  x0 = x0 ^ t ^ (t <<  4)@
 and		\t, #0x00F000F0
    eors	\x0, \x0, \t
    eor		\x0, \x0, \t, LSL #4

    eor		\t, \x0, \x0, LSR #2	@ t = (x0 ^ (x0 >>  2)) & 0x0C0C0C0CUL@  x0 = x0 ^ t ^ (t <<  2)@
 and		\t, #0x0C0C0C0C
    eors	\x0, \x0, \t
    eor		\x0, \x0, \t, LSL #2

    eor		\t, \x0, \x0, LSR #1	@ t = (x0 ^ (x0 >>  1)) & 0x22222222UL@  x0 = x0 ^ t ^ (t <<  1)@
 and		\t, #0x22222222
    eors	\x0, \x0, \t
    eor		\x0, \x0, \t, LSL #1

    eor		\t, \x1, \x1, LSR #8    @ t = (x1 ^ (x1 >>  8)) & 0x0000FF00UL@  x1 = x1 ^ t ^ (t <<  8)@
 and		\t, #0x0000FF00
    eors	\x1, \x1, \t
    eor		\x1, \x1, \t, LSL #8

    eor		\t, \x1, \x1, LSR #4	@ t = (x1 ^ (x1 >>  4)) & 0x00F000F0UL@  x1 = x1 ^ t ^ (t <<  4)@
 and		\t, #0x00F000F0
    eors	\x1, \x1, \t
    eor		\x1, \x1, \t, LSL #4

    eor		\t, \x1, \x1, LSR #2	@ t = (x1 ^ (x1 >>  2)) & 0x0C0C0C0CUL@  x1 = x1 ^ t ^ (t <<  2)@
 and		\t, #0x0C0C0C0C
    eors	\x1, \x1, \t
    eor		\x1, \x1, \t, LSL #2

    eor		\t, \x1, \x1, LSR #1	@ t = (x1 ^ (x1 >>  1)) & 0x22222222UL@  x1 = x1 ^ t ^ (t <<  1)@
 and		\t, #0x22222222
    eors	\x1, \x1, \t
    eor		\x1, \x1, \t, LSL #1
 .endm

@----------------------------------------------------------------------------
@
@ void KeccakF1600_StateExtractBytes(void *state, const unsigned char *data, unsigned int offset, unsigned int length)
@
.align 8
.global   MLK_ASM_NAMESPACE(KeccakF1600_StateExtractBytes)
.type MLK_ASM_NAMESPACE(KeccakF1600_StateExtractBytes),%function
MLK_ASM_FN_SYMBOL(KeccakF1600_StateExtractBytes)
 cbz		r3, KeccakF1600_StateExtractBytes_Exit1	@ .if length != 0
 push	{r4 - r8, lr}							@ then
 bic		r4, r2, #7								@ offset &= ~7
 adds	r0, r0, r4								@ add whole lane offset to state pointer
 ands	r2, r2, #7								@ offset &= 7 (part not lane aligned)
 beq		KeccakF1600_StateExtractBytes_CheckLanes	@ .if offset != 0
 movs	r4, r3									@ then, do remaining bytes in first lane
 rsb		r5, r2, #8								@ max size in lane = 8 - offset
 cmp		r4, r5
 ble		KeccakF1600_StateExtractBytes_BytesAlign
 movs	r4, r5
KeccakF1600_StateExtractBytes_BytesAlign:
 sub		r8, r3, r4								@ size left
 movs	r3, r4
 bl		KeccakF1600_StateExtractBytes__KeccakF1600_StateExtractBytesInLane
 mov		r3, r8
KeccakF1600_StateExtractBytes_CheckLanes:
 lsrs	r2, r3, #3								@ .if length >= 8
 beq		KeccakF1600_StateExtractBytes_Bytes
 mov		r8, r3
 bl		KeccakF1600_StateExtractBytes__KeccakF1600_StateExtractLanes
 and		r3, r8, #7
KeccakF1600_StateExtractBytes_Bytes:
 cbz		r3, KeccakF1600_StateExtractBytes_Exit
 movs	r2, #0
 bl		KeccakF1600_StateExtractBytes__KeccakF1600_StateExtractBytesInLane
KeccakF1600_StateExtractBytes_Exit:
 pop		{r4 - r8, pc}
KeccakF1600_StateExtractBytes_Exit1:
 bx		lr


@----------------------------------------------------------------------------
@
@ __KeccakF1600_StateExtractLanes
@
@ Input:
@  r0 state pointer
@  r1 data pointer
@  r2 laneCount
@
@ Output:
@  r0 state pointer next lane
@  r1 data pointer next byte to input
@
@ Changed: r2-r5
@
.align 8
KeccakF1600_StateExtractBytes__KeccakF1600_StateExtractLanes:
KeccakF1600_StateExtractBytes__KeccakF1600_StateExtractLanes_LoopAligned:
 ldrd	r4, r5, [r0], #8
 fromBitInterleaving	r4, r5, r3
 str		r4, [r1], #4
 subs	r2, r2, #1
 str		r5, [r1], #4
 bne		KeccakF1600_StateExtractBytes__KeccakF1600_StateExtractLanes_LoopAligned
 bx		lr


@----------------------------------------------------------------------------
@
@ __KeccakF1600_StateExtractBytesInLane
@
@ Input:
@  r0 state pointer
@  r1 data pointer
@  r2 offset in lane
@  r3 length
@
@ Output:
@  r0 state pointer next lane
@  r1 data pointer next byte to input
@
@  Changed: r2-r6
@
.align 8
KeccakF1600_StateExtractBytes__KeccakF1600_StateExtractBytesInLane:
 ldrd	r4, r5, [r0], #8
 fromBitInterleaving	r4, r5, r6
 push	{r4, r5}
 add		r2, sp, r2
KeccakF1600_StateExtractBytes__KeccakF1600_StateExtractBytesInLane_Loop:
 ldrb	r4, [r2], #1
 subs	r3, r3, #1
 strb	r4, [r1], #1
 bne		KeccakF1600_StateExtractBytes__KeccakF1600_StateExtractBytesInLane_Loop
 add		sp, #8
 bx		lr

#endif /* MLK_FIPS202_ARMV81M_NEED_X1 && !MLK_CONFIG_MULTILEVEL_NO_SHARED */
