/*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */

/*
 * Zephyr entrypoint shim for RAM-loaded NUCLEO-N657X0-Q tests.
 *
 * The OpenOCD/GDB wrapper breaks at get_bootargs() after Zephyr has cleared
 * BSS, restores a Zephyr dynamic bootargs command line into
 * mlk_bootargs_block, then continues. Zephyr parses the command line and calls
 * main(argc, argv). Target stdout/stderr goes through ITM stimulus port 0 and
 * is captured by the host over SWO. The test return code is passed to
 * nucleo_test_done(), where the host wrapper reads r0.
 */

#include <cmsis_core.h>
#include <stdarg.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#include <stm32n6xx_ll_bus.h>
#include <stm32n6xx_ll_gpio.h>
#include <stm32n6xx_ll_system.h>
#include <string.h>

extern int mlk_test_main(int argc, char **argv);

void nucleo_test_breakpoint(int rc);
int __wrap_printf(const char *format, ...);
int __wrap_fprintf(FILE *stream, const char *format, ...);
int __wrap_puts(const char *s);
int __wrap_putchar(int c);
int __wrap_fflush(FILE *stream);
__attribute__((noreturn)) void nucleo_test_done(int rc);
__attribute__((noreturn)) void __wrap_exit(int status);
const char *get_bootargs(void);

#define BOOTARGS_BLOCK_SIZE (64U * 1024U)
#define NUCLEO_ITM_LAR (*(volatile uint32_t *)0xE0000FB0UL)

__asm__(
    ".global mlk_bootargs_block\n"
    ".set mlk_bootargs_block, 0x340b0000\n");

extern char mlk_bootargs_block[BOOTARGS_BLOCK_SIZE];

static char nucleo_stdout_buf[8192];
static size_t nucleo_stdout_len;
static bool nucleo_swo_enabled;

/*
 * Zephyr calls this before stack setup or normal RAM initialization. The
 * NUCLEO runner has already expanded DTCM to 256 KiB, and the image now keeps
 * runtime data/stacks there, so scrub the whole DTCM window before Zephyr's
 * early stack, BSS, and MPU setup touch it.
 */
__attribute__((naked, used)) void soc_early_reset_hook(void)
{
  __asm__ volatile(
      "movs r2, #0\n"
      "movs r3, #0\n"
      "ldr r0, =0x30000000\n"
      "ldr r1, =0x30040000\n"
      "1:\n"
      "strd r2, r3, [r0], #8\n"
      "cmp r0, r1\n"
      "blo 1b\n"
      "dsb\n"
      "isb\n"
      "bx lr\n");
}

static void nucleo_swo_pin_setup(void)
{
  LL_AHB4_GRP1_EnableClock(LL_AHB4_GRP1_PERIPH_GPIOB);
  LL_GPIO_SetPinMode(GPIOB, LL_GPIO_PIN_5, LL_GPIO_MODE_ALTERNATE);
  LL_GPIO_SetPinSpeed(GPIOB, LL_GPIO_PIN_5, LL_GPIO_SPEED_FREQ_VERY_HIGH);
  LL_GPIO_SetPinPull(GPIOB, LL_GPIO_PIN_5, LL_GPIO_PULL_NO);
  LL_GPIO_SetAFPin_0_7(GPIOB, LL_GPIO_PIN_5, LL_GPIO_AF_0);
}

static void nucleo_swo_enable(void)
{
  if (nucleo_swo_enabled)
  {
    return;
  }

  nucleo_swo_pin_setup();
  LL_BUS_EnableClock(LL_APB3);
  LL_DBGMCU_EnableDBGClock();
  LL_DBGMCU_EnableTPIUExportClock();
  CoreDebug->DEMCR |= CoreDebug_DEMCR_TRCENA_Msk;

  NUCLEO_ITM_LAR = 0xC5ACCE55UL;
  ITM->TER = 0UL;
  ITM->TCR &= ~ITM_TCR_ITMENA_Msk;
  while ((ITM->TCR & ITM_TCR_BUSY_Msk) != 0UL)
  {
  }
  ITM->TPR = 0UL;
  ITM->TCR =
      ITM_TCR_ITMENA_Msk | ITM_TCR_DWTENA_Msk | (1UL << ITM_TCR_TRACEBUSID_Pos);
  ITM->TER = 1UL;
  nucleo_swo_enabled = true;
}

static void nucleo_swo_write_byte(char ch)
{
  nucleo_swo_enable();

  if (((ITM->TCR & ITM_TCR_ITMENA_Msk) == 0UL) || ((ITM->TER & 1UL) == 0UL))
  {
    return;
  }

  while (ITM->PORT[0U].u32 == 0UL)
  {
  }
  ITM->PORT[0U].u8 = (uint8_t)ch;
}

static void nucleo_swo_write_raw(const char *src, size_t len)
{
  for (size_t offset = 0; offset < len; offset++)
  {
    nucleo_swo_write_byte(src[offset]);
  }
}

static void nucleo_swo_wait_idle(void)
{
  for (uint32_t timeout = 10000000UL; timeout > 0U; timeout--)
  {
    if ((ITM->TCR & ITM_TCR_BUSY_Msk) == 0UL)
    {
      break;
    }
  }
  __DSB();
}

__attribute__((noinline, used)) void nucleo_test_breakpoint(int rc)
{
  (void)rc;
  __asm__ volatile("bkpt 0" ::: "memory");
}

static void nucleo_stdout_flush(void)
{
  if (nucleo_stdout_len == 0U)
  {
    return;
  }

  nucleo_swo_write_raw(nucleo_stdout_buf, nucleo_stdout_len);
  nucleo_stdout_len = 0U;
}

static void nucleo_stdout_write(const char *src, size_t len)
{
  for (size_t i = 0; i < len; i++)
  {
    nucleo_stdout_buf[nucleo_stdout_len++] = src[i];
    if (src[i] == '\n' || nucleo_stdout_len == sizeof(nucleo_stdout_buf))
    {
      nucleo_stdout_flush();
    }
  }
}

static int nucleo_vprintf(const char *format, va_list ap)
{
  char buf[8192];
  int rc = vsnprintf(buf, sizeof(buf), format, ap);

  if (rc <= 0)
  {
    return rc;
  }

  nucleo_stdout_write(
      buf, (size_t)((rc < (int)sizeof(buf)) ? rc : (int)sizeof(buf) - 1));
  return rc;
}

int __wrap_printf(const char *format, ...)
{
  va_list ap;
  int rc;

  va_start(ap, format);
  rc = nucleo_vprintf(format, ap);
  va_end(ap);
  return rc;
}

int __wrap_fprintf(FILE *stream, const char *format, ...)
{
  va_list ap;
  int rc;

  (void)stream;
  va_start(ap, format);
  rc = nucleo_vprintf(format, ap);
  va_end(ap);
  return rc;
}

int __wrap_puts(const char *s)
{
  size_t len = strlen(s);

  nucleo_stdout_write(s, len);
  nucleo_stdout_write("\n", 1);
  return (int)len + 1;
}

int __wrap_putchar(int c)
{
  char ch = (char)c;

  nucleo_stdout_write(&ch, 1);
  return c;
}

int __wrap_fflush(FILE *stream)
{
  (void)stream;
  nucleo_stdout_flush();
  return 0;
}

__attribute__((noreturn, noinline, used)) void nucleo_test_done(int rc)
{
  nucleo_stdout_flush();
  nucleo_swo_wait_idle();
  nucleo_test_breakpoint(rc);
  for (;;)
  {
    __WFI();
  }
}

__attribute__((noreturn)) void __wrap_exit(int status)
{
  nucleo_test_done(status);
}

__attribute__((noinline, used)) const char *get_bootargs(void)
{
  return mlk_bootargs_block;
}

int main(int argc, char **argv)
{
  int rc = mlk_test_main(argc, argv);

  nucleo_test_done(rc);
}
