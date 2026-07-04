/*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */

#ifndef _STDDEF_H
#define _STDDEF_H 1

/* "LP64" stands for "Long and Pointer are 64-bit", so
 *  size_t is "unsigned long" which has the same size as a "pointer"
 */
typedef unsigned long size_t;

#define NULL (0)

#endif /* !_STDDEF_H */
