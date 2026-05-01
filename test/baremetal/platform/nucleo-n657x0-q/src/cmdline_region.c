/*
 * Copyright (c) The mldsa-native project authors
 * Copyright (c) The mlkem-native project authors
 * Copyright (c) Arm Ltd.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */
#include <stdint.h>
/* Argv block in I-TCM; populated by GDB after C startup reaches __wrap_main. */
__attribute__((aligned(8), used, section(".cmdline")))
unsigned char mlk_cmdline_block[64 * 1024];
