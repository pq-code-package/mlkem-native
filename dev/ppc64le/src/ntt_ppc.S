/*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */

#
# Copyright 2025- IBM Corp.
#
#===================================================================================
# Written by Danny Tsen <dtsen@us.ibm.com>
#

#include "../../../common.h"
#if defined(MLK_ARITH_BACKEND_PPC64LE_DEFAULT) && \
    !defined(MLK_CONFIG_MULTILEVEL_NO_SHARED)
/* simpasm: header-end */

#include "consts.h"

#define V_QINV  2
#define V_NMKQ  5
#define	V_Z0    7
#define	V_Z1    8
#define	V_Z2    9
#define	V_Z3    10
#define V_ZETA  10

.machine "any"
.text

#
# montgomery_reduce
# t = a * QINV
# t = (a - (int32_t)t*_MLKEM_Q) >> 16
#
#-----------------------------------
# MREDUCE_4X(start, _vz0, _vz1, _vz2, _vz3)
#
.macro MREDUCE_4X start next step _vz0 _vz1 _vz2 _vz3
	mr	9, \start
	add	10, 7, 9	# J + len*2
	addi	16, 9, \next
	addi	17, 10, \step
	addi	18, 16, \next
	addi	19, 17, \step
	addi	20, 18, \next
	addi	21, 19, \step
	lxvd2x	32+13, 3, 10	# r[j+len]
	lxvd2x	32+18, 3, 17	# r[j+len]
	lxvd2x	32+23, 3, 19	# r[j+len]
	lxvd2x	32+28, 3, 21	# r[j+len]
	xxpermdi 32+13, 32+13, 32+13, 2
	xxpermdi 32+18, 32+18, 32+18, 2
	xxpermdi 32+23, 32+23, 32+23, 2
	xxpermdi 32+28, 32+28, 32+28, 2

	# fqmul = zeta * coefficient
	# Modular multification bond by 2^16 * q in abs value
	vmladduhm 15, 13, \_vz0, 3
	vmladduhm 20, 18, \_vz1, 3
	vmladduhm 25, 23, \_vz2, 3
	vmladduhm 30, 28, \_vz3, 3

	# Signed multiply-high-round; outputs are bound by 2^15 * q in abs value
	vmhraddshs 14, 13, \_vz0, 3
	vmhraddshs 19, 18, \_vz1, 3
	vmhraddshs 24, 23, \_vz2, 3
	vmhraddshs 29, 28, \_vz3, 3

	vmladduhm 15, 15, V_QINV, 3
	vmladduhm 20, 20, V_QINV, 3
	vmladduhm 25, 25, V_QINV, 3
	vmladduhm 30, 30, V_QINV, 3

	vmhraddshs 15, 15, V_NMKQ, 14
	vmhraddshs 20, 20, V_NMKQ, 19
	vmhraddshs 25, 25, V_NMKQ, 24
	vmhraddshs 30, 30, V_NMKQ, 29

	vsrah 13, 15, 4		# >> 1
	vsrah 18, 20, 4		# >> 1
	vsrah 23, 25, 4		# >> 1
	vsrah 28, 30, 4		# >> 1

	lxvd2x	32+12, 3, 9	# r[j]
	lxvd2x	32+17, 3, 16	# r[j]
	lxvd2x	32+22, 3, 18	# r[j]
	lxvd2x	32+27, 3, 20	# r[j]
	xxpermdi 32+12, 32+12, 32+12, 2
	xxpermdi 32+17, 32+17, 32+17, 2
	xxpermdi 32+22, 32+22, 32+22, 2
	xxpermdi 32+27, 32+27, 32+27, 2

	# Since the result of the Montgomery multiplication is bounded
	# by q in absolute value.
	# Finally to complete the final update of the results with add/sub
	vsubuhm 16, 12, 13		# r - t
	vadduhm 15, 13, 12		# r + t
	vsubuhm 21, 17, 18		# r - t
	vadduhm 20, 18, 17		# r + t
	vsubuhm 26, 22, 23		# r - t
	vadduhm 25, 23, 22		# r + t
	vsubuhm 31, 27, 28		# r - t
	vadduhm 30, 28, 27		# r + t
.endm

.macro Write_One
	stxvx 32+15, 3, 9
	stxvx 32+16, 3, 10
	stxvx 32+20, 3, 16
	stxvx 32+21, 3, 17
	stxvx 32+25, 3, 18
	stxvx 32+26, 3, 19
	stxvx 32+30, 3, 20
	stxvx 32+31, 3, 21
.endm

.macro Write_Two
	xxpermdi 32+17, 32+16, 32+15, 3
	xxpermdi 32+22, 32+21, 32+20, 3
	xxpermdi 32+27, 32+26, 32+25, 3
	xxpermdi 32+29, 32+31, 32+30, 3

	stxvx	32+17, 3, 9
	stxvx	32+22, 3, 16
	stxvx	32+27, 3, 18
	stxvx	32+29, 3, 20
.endm

.macro Write_Three
	xxmrglw	32+14, 32+16, 32+15
	xxmrghw	32+13, 32+16, 32+15
	xxpermdi 32+17, 32+13, 32+14, 3
	xxmrglw	32+19, 32+21, 32+20
	xxmrghw	32+18, 32+21, 32+20
	xxpermdi 32+22, 32+18, 32+19, 3
	xxmrglw	32+14, 32+26, 32+25
	xxmrghw	32+13, 32+26, 32+25
	xxpermdi 32+27, 32+13, 32+14, 3
	xxmrglw	32+24, 32+31, 32+30
	xxmrghw	32+23, 32+31, 32+30
	xxpermdi 32+29, 32+23, 32+24, 3
	stxvx	32+17, 3, 9
	stxvx	32+22, 3, 16
	stxvx	32+27, 3, 18
	stxvx	32+29, 3, 20
.endm

.macro Load_next_4zetas
	lxv	32+V_Z0, 0(14)
	lxv	32+V_Z1, 16(14)
	lxv	32+V_Z2, 32(14)
	lxv	32+V_Z3, 48(14)
	addi	14, 14, 64
.endm

#
# mlk_ntt_ppc(int16_t *r)
#
.global MLK_ASM_NAMESPACE(ntt_ppc)
.align 4
MLK_ASM_FN_SYMBOL(ntt_ppc)

	stdu	1, -352(1)
	mflr	0
	std	14, 56(1)
	std	15, 64(1)
	std	16, 72(1)
	std	17, 80(1)
	std	18, 88(1)
	std	19, 96(1)
	std	20, 104(1)
	std	21, 112(1)
	stxv	32+20, 128(1)
	stxv	32+21, 144(1)
	stxv	32+22, 160(1)
	stxv	32+23, 176(1)
	stxv	32+24, 192(1)
	stxv	32+25, 208(1)
	stxv	32+26, 224(1)
	stxv	32+27, 240(1)
	stxv	32+28, 256(1)
	stxv	32+29, 272(1)
	stxv	32+30, 288(1)
	stxv	32+31, 304(1)

	# get MLKEM_Q
	lvx	V_NMKQ,0,4

	# zetas array
	addi	14, 4, ZETA_NTT_OFFSET

	vxor	3, 3, 3
	vspltish 4, 1

	lxv	32+V_QINV, QINV_OFFSET(4)

.align 4
	#
	# Compute coefficients of the NTT based on the following loop.
	#   for (len = 128; len ≥ 2; len =  len/2)
	#
	# 1. len = 128, start = 0
	#
	li	5, 0		# start
	li	7, 256		# len * 2
	lvx	V_ZETA, 0, 14
	addi	14, 14, 16

	MREDUCE_4X 5, 16, 16, V_ZETA, V_ZETA, V_ZETA, V_ZETA
	Write_One
	li	5, 64
	MREDUCE_4X 5, 16, 16, V_ZETA, V_ZETA, V_ZETA, V_ZETA
	Write_One
	li	5, 128
	MREDUCE_4X 5, 16, 16, V_ZETA, V_ZETA, V_ZETA, V_ZETA
	Write_One
	li	5, 192
	MREDUCE_4X 5, 16, 16, V_ZETA, V_ZETA, V_ZETA, V_ZETA
	Write_One

.align 4
	#
	# 2. len = 64, start = 0, 128
	# k += 2
	li	5, 0
	li	7, 128
	lvx	V_ZETA, 0, 14
	addi	14, 14, 16
	MREDUCE_4X 5, 16, 16, V_ZETA, V_ZETA, V_ZETA, V_ZETA
	Write_One
	li	5, 64
	MREDUCE_4X 5, 16, 16, V_ZETA, V_ZETA, V_ZETA, V_ZETA
	Write_One
	li	5, 256

	lvx	V_ZETA, 0, 14
	addi	14, 14, 16
	MREDUCE_4X 5, 16, 16, V_ZETA, V_ZETA, V_ZETA, V_ZETA
	Write_One
	li	5, 320
	MREDUCE_4X 5, 16, 16, V_ZETA, V_ZETA, V_ZETA, V_ZETA
	Write_One

.align 4
	#
	# 3. len = 32, start = 0, 64, 128, 192
	# k += 4
	li	5, 0
	li	7, 64
	lvx	V_ZETA, 0, 14
	addi	14, 14, 16
	MREDUCE_4X 5, 16, 16, V_ZETA, V_ZETA, V_ZETA, V_ZETA
	Write_One
	#li	5, 64
	li	5, 128

	lvx	V_ZETA, 0, 14
	addi	14, 14, 16
	MREDUCE_4X 5, 16, 16, V_ZETA, V_ZETA, V_ZETA, V_ZETA
	Write_One
	#li	5, 128
	li	5, 256

	lvx	V_ZETA, 0, 14
	addi	14, 14, 16
	MREDUCE_4X 5, 16, 16, V_ZETA, V_ZETA, V_ZETA, V_ZETA
	Write_One
	#li	5, 192
	li	5, 384

	lvx	V_ZETA, 0, 14
	addi	14, 14, 16
	MREDUCE_4X 5, 16, 16, V_ZETA, V_ZETA, V_ZETA, V_ZETA
	Write_One

.align 4
	#
	# 4. len = 16, start = 0, 32, 64,,...160, 192, 224
	# k += 8
	li	5, 0
	li	7, 32
	Load_next_4zetas
	MREDUCE_4X 5, 64, 64, V_Z0, V_Z1, V_Z2, V_Z3
	Write_One
	li	5, 16
	MREDUCE_4X 5, 64, 64, V_Z0, V_Z1, V_Z2, V_Z3
	Write_One

	Load_next_4zetas
	li	5, 256
	MREDUCE_4X 5, 64, 64, V_Z0, V_Z1, V_Z2, V_Z3
	Write_One
	li	5, 272
	MREDUCE_4X  5, 64, 64, V_Z0, V_Z1, V_Z2, V_Z3
	Write_One

.align 4
	#
	# 5. len = 8, start = 0, 16, 32, 48,...208, 224, 240 
	# k += 16
	li	5, 0
	li	7, 16
	Load_next_4zetas
	MREDUCE_4X 5, 32, 32, V_Z0, V_Z1, V_Z2, V_Z3
	Write_One
	li	5, 128

	Load_next_4zetas
	MREDUCE_4X 5, 32, 32, V_Z0, V_Z1, V_Z2, V_Z3
	Write_One
	li	5, 256

	Load_next_4zetas
	MREDUCE_4X 5, 32, 32, V_Z0, V_Z1, V_Z2, V_Z3
	Write_One
	li	5, 384

	Load_next_4zetas
	MREDUCE_4X 5, 32, 32, V_Z0, V_Z1, V_Z2, V_Z3
	Write_One

	#
	# 6. len = 4, start = 0, 8, 16, 24,...232, 240, 248 
	# k += 32
	li	15, 4			# loops
	mtctr	15
	li	5, 0
	li	7, 8
.align 4
ntt_ppc__Len4:
	Load_next_4zetas
	MREDUCE_4X 5, 16, 16, V_Z0, V_Z1, V_Z2, V_Z3
	Write_Two
	addi	5, 5, 64

	Load_next_4zetas
	MREDUCE_4X 5, 16, 16, V_Z0, V_Z1, V_Z2, V_Z3
	Write_Two
	addi	5, 5, 64

	bdnz	ntt_ppc__Len4

	#
	# 7. len = 2, start = 0, 4, 8, 12,...244, 248, 252 
	# k += 64
	# Update zetas vectors, each vector has 2 zetas

	addi	14, 4, ZETA_NTT_OFFSET64

	li	15, 4
	mtctr	15
	li	5, 0
	li	7, 4
.align 4
ntt_ppc__Len2:
	Load_next_4zetas
	MREDUCE_4X 5, 16, 16, V_Z0, V_Z1, V_Z2, V_Z3
	Write_Three
	addi	5, 5, 64

	Load_next_4zetas
	MREDUCE_4X 5, 16, 16, V_Z0, V_Z1, V_Z2, V_Z3
	Write_Three
	addi	5, 5, 64

	bdnz	ntt_ppc__Len2

	lxv	32+20, 128(1)
	lxv	32+21, 144(1)
	lxv	32+22, 160(1)
	lxv	32+23, 176(1)
	lxv	32+24, 192(1)
	lxv	32+25, 208(1)
	lxv	32+26, 224(1)
	lxv	32+27, 240(1)
	lxv	32+28, 256(1)
	lxv	32+29, 272(1)
	lxv	32+30, 288(1)
	lxv	32+31, 304(1)
	ld	14, 56(1)
	ld	15, 64(1)
	ld	16, 72(1)
	ld	16, 72(1)
	ld	17, 80(1)
	ld	18, 88(1)
	ld	19, 96(1)
	ld	20, 104(1)
	ld	21, 112(1)

	mtlr	0
	addi    1, 1, 352
	blr

/* To facilitate single-compilation-unit (SCU) builds, undefine all macros.
 * Don't modify by hand -- this is auto-generated by scripts/autogen. */
#undef V_QINV
#undef V_NMKQ
#undef V_ZETA

/* simpasm: footer-start */
#endif /* MLK_ARITH_BACKEND_PPC64LE_DEFAULT && \
          !MLK_CONFIG_MULTILEVEL_NO_SHARED */
