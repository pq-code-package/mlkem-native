/*
 * Copyright (c) The mldsa-native project authors
 * Copyright (c) The mlkem-native project authors
 * Copyright (c) Arm Ltd.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */
#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#include "stm32n6xx.h"
#include "stm32n6xx_hal.h"
#include "stm32n6xx_it.h"
#include "main.h"

typedef struct cmdline_s {
  int argc;
  char *argv[];
} cmdline_t;

/* Allow overriding CMDLINE_ADDR; default matches AN547 usage. */
#ifndef CMDLINE_ADDR
#define CMDLINE_ADDR ((cmdline_t *)0x70000)
#endif

/* Provided by cmdline_region.c */
extern unsigned char mlk_cmdline_block[];

/* Provide a prototype for the real main that the C library expects. */
extern int __real_main(int argc, char *argv[]);
int __wrap_main(int unused_argc, char *unused_argv[]);

#ifdef SEMIHOSTING
#include "semihosting_syscall.h"
static void semihosting_exit_with_rc(int rc) {
  // Print sentinel for the exec_wrapper to detect and propagate exit code
  printf("[[MLKEM-EXIT:%d]]\n",rc);
  fflush(stdout);
  // Try basic semihost exit (ST-LINK may or may not support it). If unsupported,
  // gdbserver may report an error; wrapper already captured the code.
  while(1) ;
}
#else
static void semihosting_exit_with_rc(int rc) { (void)rc; }
#endif

void Error_Handler(void) {
  HardFault_Handler();
}

/* Wrap main: build argc/argv from cmdline and forward to __real_main. */
int __wrap_main(int unused_argc, char *unused_argv[]) {
  (void)unused_argc; (void)unused_argv;
  SCB_EnableICache();
  SCB_EnableDCache();
  HAL_Init();
  SystemClock_Config();

  cmdline_t *cmdline = (cmdline_t *)&mlk_cmdline_block;
  int rc = __real_main(cmdline->argc, cmdline->argv);
  semihosting_exit_with_rc(rc);
  return rc;
}

