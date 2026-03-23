/*
 * Copyright (c) The mldsa-native project authors
 * Copyright (c) The mlkem-native project authors
 * Copyright (c) Arm Ltd.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */
#include <stdint.h>
/* 64 KiB command-line buffer in BSS, 8-byte aligned */
__attribute__((aligned(8), used))
unsigned char mlk_cmdline_block[64 * 1024];
