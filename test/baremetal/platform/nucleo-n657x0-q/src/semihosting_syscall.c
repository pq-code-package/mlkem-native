/*
 * Copyright (c) The mldsa-native project authors
 * Copyright (c) The mlkem-native project authors
 * Copyright (c) Arm Ltd.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */
#include <stdio.h>
#include <stdint.h>
/* Public semihosting API */
#include "semihosting_syscall.h"
__attribute__((always_inline)) static inline void __semihosting_call(int32_t opnr, int32_t param) {
  register int32_t r0 __asm__("r0") = opnr;
  register int32_t r1 __asm__("r1") = param;
  __asm__ __volatile__("bkpt 0xAB" : "+r"(r0) : "r"(r1) : "memory");
}
void semihosting_syscall(int32_t opnr, int32_t param) {
  __semihosting_call(opnr, param);
}

// Provided by --specs=rdimon.specs
extern void initialise_monitor_handles(void);

__attribute__((constructor))
static void mlkem_semihost_init(void) {
  initialise_monitor_handles();
  fflush(stdout);
}
