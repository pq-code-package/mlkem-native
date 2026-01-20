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
.macro	toBitInterleaving	x0,x1,s0,s1,t,over

 and		\t,\x0,#0x55555555
 orr		\t,\t,\t, LSR #1
 and		\t,\t,#0x33333333
 orr		\t,\t,\t, LSR #2
 and		\t,\t,#0x0F0F0F0F
 orr		\t,\t,\t, LSR #4
 and		\t,\t,#0x00FF00FF
 bfi		\t,\t,#8, #8
 .if \over != 0
 lsr		\s0,\t, #8
 .else
 eor		\s0,\s0,\t, LSR #8
 .endif

 and		\t,\x1,#0x55555555
 orr		\t,\t,\t, LSR #1
 and		\t,\t,#0x33333333
 orr		\t,\t,\t, LSR #2
 and		\t,\t,#0x0F0F0F0F
 orr		\t,\t,\t, LSR #4
 and		\t,\t,#0x00FF00FF
 orr		\t,\t,\t, LSR #8
 eor		\s0,\s0,\t, LSL #16

 and		\t,\x0,#0xAAAAAAAA
 orr		\t,\t,\t, LSL #1
 and		\t,\t,#0xCCCCCCCC
 orr		\t,\t,\t, LSL #2
 and		\t,\t,#0xF0F0F0F0
 orr		\t,\t,\t, LSL #4
 and		\t,\t,#0xFF00FF00
 orr		\t,\t,\t, LSL #8
 .if \over != 0
 lsr		\s1,\t, #16
 .else
 eor		\s1,\s1,\t, LSR #16
 .endif

 and		\t,\x1,#0xAAAAAAAA
 orr		\t,\t,\t, LSL #1
 and		\t,\t,#0xCCCCCCCC
 orr		\t,\t,\t, LSL #2
 and		\t,\t,#0xF0F0F0F0
 orr		\t,\t,\t, LSL #4
 and		\t,\t,#0xFF00FF00
 orr		\t,\t,\t, LSL #8
 bfc		\t, #0, #16
 eors	\s1,\s1,\t
.endm

@----------------------------------------------------------------------------
@
@ void KeccakF1600_StateXORBytes(void *state, const unsigned char *data, unsigned int offset, unsigned int length)
@
.align 8
.global   MLK_ASM_NAMESPACE(KeccakF1600_StateXORBytes)
.type MLK_ASM_NAMESPACE(KeccakF1600_StateXORBytes),%function
MLK_ASM_FN_SYMBOL(KeccakF1600_StateXORBytes)
 cbz		r3, KeccakF1600_StateXORBytes_Exit1
 push	{r4 - r8, lr}							@ then
 bic		r4, r2, #7								@ offset &= ~7
 adds	r0, r0, r4								@ add whole lane offset to state pointer
 ands	r2, r2, #7								@ offset &= 7 (part not lane aligned)
 beq		KeccakF1600_StateXORBytes_CheckLanes	@ .if offset != 0
 movs	r4, r3									@ then, do remaining bytes in first lane
 rsb		r5, r2, #8								@ max size in lane = 8 - offset
 cmp		r4, r5
 ble		KeccakF1600_StateXORBytes_BytesAlign
 movs	r4, r5
KeccakF1600_StateXORBytes_BytesAlign:
 sub		r8, r3, r4								@ size left
 movs	r3, r4
 bl		KeccakF1600_StateXORBytes__KeccakF1600_StateXORBytesInLane
 mov		r3, r8
KeccakF1600_StateXORBytes_CheckLanes:
 lsrs	r2, r3, #3								@ .if length >= 8
 beq		KeccakF1600_StateXORBytes_Bytes
 mov		r8, r3
 bl		KeccakF1600_StateXORBytes__KeccakF1600_StateXORLanes
 and		r3, r8, #7
KeccakF1600_StateXORBytes_Bytes:
 cbz		r3, KeccakF1600_StateXORBytes_Exit
 movs	r2, #0
 bl		KeccakF1600_StateXORBytes__KeccakF1600_StateXORBytesInLane
KeccakF1600_StateXORBytes_Exit:
 pop		{r4 - r8, pc}
KeccakF1600_StateXORBytes_Exit1:
 bx		lr


@----------------------------------------------------------------------------
@
@ __KeccakF1600_StateXORLanes
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
@ Changed: r2-r7
@
.align 8
KeccakF1600_StateXORBytes__KeccakF1600_StateXORLanes:
KeccakF1600_StateXORBytes__KeccakF1600_StateXORLanes_LoopAligned:
 ldr		r4, [r1], #4
 ldr		r5, [r1], #4
 ldrd    r6, r7, [r0]
 toBitInterleaving	r4, r5, r6, r7, r3, 0
 strd	r6, r7, [r0], #8
 subs	r2, r2, #1
 bne		KeccakF1600_StateXORBytes__KeccakF1600_StateXORLanes_LoopAligned
 bx		lr


@----------------------------------------------------------------------------
@
@ __KeccakF1600_StateXORBytesInLane
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
@  Changed: r2-r7
@
.align 8
KeccakF1600_StateXORBytes__KeccakF1600_StateXORBytesInLane:
 movs	r4, #0
 movs	r5, #0
 push	{ r4 - r5 }
 add		r2, r2, sp
KeccakF1600_StateXORBytes__KeccakF1600_StateXORBytesInLane_Loop:
 ldrb	r5, [r1], #1
 strb	r5, [r2], #1
 subs	r3, r3, #1
 bne		KeccakF1600_StateXORBytes__KeccakF1600_StateXORBytesInLane_Loop
 pop		{ r4 - r5 }
 ldrd    r6, r7, [r0]
 toBitInterleaving	r4, r5, r6, r7, r3, 0
 strd	r6, r7, [r0], #8
 bx		lr


#endif /* MLK_FIPS202_ARMV81M_NEED_X1 && !MLK_CONFIG_MULTILEVEL_NO_SHARED */
