/*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */
#include <stdint.h>

__attribute__((section(".itcm_probe"), noinline, used))
static uint32_t nucleo_itcm_above_default_probe(uint32_t x)
{
  return x ^ 0xa5a55a5aUL;
}

__attribute__((noinline, used))
void nucleo_layout_fail(uint32_t code)
{
  __asm__ volatile("mov r0, %0\n"
                   "bkpt 0\n" : : "r"(code) : "r0", "memory");
  for (;;) {
  }
}

void nucleo_flexmem_layout_check(void)
{
  volatile uint32_t *dtcm_above_default = (volatile uint32_t *)0x30020000UL;
  const uint32_t saved = *dtcm_above_default;
  uint32_t probe;

  *dtcm_above_default = 0x5aa55aa5UL;
  __asm__ volatile("dsb sy" ::: "memory");
  probe = *dtcm_above_default;
  *dtcm_above_default = saved;

  if (probe != 0x5aa55aa5UL) {
    nucleo_layout_fail(1);
  }

  if (nucleo_itcm_above_default_probe(0x11223344UL) != 0xb487691eUL) {
    nucleo_layout_fail(2);
  }
}
