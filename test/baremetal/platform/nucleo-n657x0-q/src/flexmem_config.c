/*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */
#include <stdint.h>

#include "stm32n6xx.h"

#ifndef SYSCFG_CM55TCMCR_CFGITCMSZ_Pos
#error "STM32N6 CMSIS header is missing SYSCFG_CM55TCMCR_CFGITCMSZ_Pos"
#endif
#ifndef SYSCFG_CM55TCMCR_CFGDTCMSZ_Pos
#error "STM32N6 CMSIS header is missing SYSCFG_CM55TCMCR_CFGDTCMSZ_Pos"
#endif
#ifndef RCC_APB4ENSR2_SYSCFGENS
#error "STM32N6 CMSIS header is missing RCC_APB4ENSR2_SYSCFGENS"
#endif

#define FLEXMEM_TCM_SIZE_256K 9UL

int main(void)
{
  const uint32_t flexmem_value =
      (FLEXMEM_TCM_SIZE_256K << SYSCFG_CM55TCMCR_CFGITCMSZ_Pos) |
      (FLEXMEM_TCM_SIZE_256K << SYSCFG_CM55TCMCR_CFGDTCMSZ_Pos);

  __disable_irq();

  RCC->APB4ENSR2 = RCC_APB4ENSR2_SYSCFGENS;
  (void)RCC->APB4ENR2;

  SYSCFG->CM55TCMCR = (SYSCFG->CM55TCMCR & ~(SYSCFG_CM55TCMCR_CFGITCMSZ_Msk |
                                             SYSCFG_CM55TCMCR_CFGDTCMSZ_Msk)) |
                      flexmem_value;
  (void)SYSCFG->CM55TCMCR;

#ifdef SYSCFG_CM55RSTCR_CORE_RESET_TYPE
  SYSCFG->CM55RSTCR |= SYSCFG_CM55RSTCR_CORE_RESET_TYPE;
  (void)SYSCFG->CM55RSTCR;
#endif

  __DSB();
  __ISB();

  __BKPT(0);
  for (;;)
  {
    __WFI();
  }
}
