/*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */

#ifndef _STDDEF_H
#define _STDDEF_H 1

/* "ILP32" stands for "Int, Long, and Pointer are 32-bit", so
 *  size_t is "unsigned long" which has the same size as a "pointer"
 */
typedef unsigned long size_t;

#define NULL (0)

#endif
