/*
 * Copyright (c) The mldsa-native project authors
 * Copyright (c) The mlkem-native project authors
 * Copyright (c) Arm Ltd.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */
#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#include "main.h"
#include "semihosting_syscall.h"
#include "stm32n6xx.h"
#include "stm32n6xx_hal.h"
#include "stm32n6xx_it.h"

typedef struct cmdline_s
{
  int argc;
  char *argv[];
} cmdline_t;

/* Allow overriding CMDLINE_ADDR; default matches AN547 usage. */
#ifndef CMDLINE_ADDR
#define CMDLINE_ADDR ((cmdline_t *)0x70000)
#endif

/* Provided by cmdline_region.c */
extern unsigned char mlk_cmdline_block[];
void nucleo_flexmem_layout_check(void);


extern unsigned char _ebss[];
extern unsigned char __StackLimit[];
extern unsigned char _estack[];

__attribute__((noinline)) static void nucleo_init_dtcm_ecc(void)
{
  uintptr_t sp;
  __asm__ volatile("mov %0, sp" : "=r"(sp));
  sp = (sp - 64U) & ~(uintptr_t)31U;
  uintptr_t heap_start = ((uintptr_t)_ebss + 31U) & ~(uintptr_t)31U;
  uintptr_t heap_end = (uintptr_t)__StackLimit & ~(uintptr_t)31U;
  if (heap_start < heap_end)
  {
    for (volatile uint32_t *ptr = (volatile uint32_t *)heap_start;
         (uintptr_t)ptr < heap_end; ptr++)
    {
      *ptr = 0;
    }
  }

  uintptr_t stack_start = ((uintptr_t)__StackLimit + 31U) & ~(uintptr_t)31U;
  uintptr_t stack_end = sp;
  if (stack_end > (uintptr_t)_estack)
  {
    stack_end = (uintptr_t)_estack;
  }
  for (volatile uint32_t *ptr = (volatile uint32_t *)stack_start;
       (uintptr_t)ptr < stack_end; ptr++)
  {
    *ptr = 0;
  }
  __DSB();
}

/* Provide a prototype for the real main that the C library expects. */
extern int __real_main(int argc, char *argv[]);
int __wrap_main(int unused_argc, char *unused_argv[]);

__attribute__((noreturn)) static void semihosting_exit_with_rc(int rc)
{
  if (rc == 0)
  {
    printf("[[MLKEM-EXIT:0]]\n");
  }
  else
  {
    printf("[[MLKEM-EXIT:1]]\n");
  }
  fflush(stdout);
  SCB_CleanDCache();
  __DSB();
  __ISB();
  __BKPT(0);
  while (1)
  {
    __WFI();
  }
}

void _exit(int status) { semihosting_exit_with_rc(status); }

void Error_Handler(void) { HardFault_Handler(); }

/* Wrap main: build argc/argv from cmdline and forward to __real_main. */
int __wrap_main(int unused_argc, char *unused_argv[])
{
  (void)unused_argc;
  (void)unused_argv;
  nucleo_init_dtcm_ecc();
  nucleo_stdio_init();
  SCB_EnableICache();
  SCB_EnableDCache();
  HAL_Init();
  SystemClock_Config();
  nucleo_flexmem_layout_check();

  cmdline_t *cmdline = (cmdline_t *)&mlk_cmdline_block;
  int rc = __real_main(cmdline->argc, cmdline->argv);
  semihosting_exit_with_rc(rc);
  return rc;
}
