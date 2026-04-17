/*
 * Copyright (c) The mldsa-native project authors
 * Copyright (c) The mlkem-native project authors
 * Copyright (c) Arm Ltd.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */
#ifndef MLKEM_NATIVE_SEMIHOSTING_SYSCALL_H
#define MLKEM_NATIVE_SEMIHOSTING_SYSCALL_H

#include <stdint.h>

void semihosting_syscall(int32_t opnr, int32_t param);

#endif /* MLKEM_NATIVE_SEMIHOSTING_SYSCALL_H */

