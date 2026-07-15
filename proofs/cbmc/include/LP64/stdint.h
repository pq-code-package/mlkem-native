/*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */

#ifndef _STDINT_H
#define _STDINT_H 1

typedef unsigned char uint8_t;
typedef signed char int8_t;

typedef unsigned short uint16_t;
typedef short int16_t;

/* "LP64" stands for "Long and Pointer are 64-bit", so
 *   int32_t is "int"
 *  uint32_t is "unsigned int"
 *   int64_t is "long"
 *  uint64_t is "unsigned long"
 * and
 *  SIZE_MAX is 2**64-1
 */
typedef unsigned int uint32_t;
typedef int int32_t;

typedef unsigned long uint64_t;
typedef long int64_t;

#define SIZE_MAX (18446744073709551615UL)

#define UINT16_MAX (65535U)
#define INT16_MAX (32767)
#define INT16_MIN (-32767 - 1)

#define INT32_MAX (2147483647)
#define UINT32_MAX (4294967295U)

#endif
