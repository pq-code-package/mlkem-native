/* Copyright (c) The mlkem-native project authors */
/* SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT */

#include <avr/eeprom.h>
#include <avr/interrupt.h>
#include <avr/io.h>
#include <avr/sleep.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include <simavr/avr/avr_mcu_section.h>

/* Register for sending commands (e.g. exit codes) to simavr */
AVR_MCU_SIMAVR_COMMAND(&GPIOR0);

/* The argc/argv block is placed at the top of RAM, just below 16 bytes of
 * scratch stack used during startup. The exec wrapper chooses the base
 * address RAM_TOP - blocksize and stores it in the first two bytes of
 * EEPROM, followed by the block itself. The stack grows downwards from
 * just below the block, so binaries with little argument data
 * automatically get the largest possible stack. */
#define RAM_TOP 0xFFF0

/* Base address of the argc/argv block, read from EEPROM. Used by the
 * argc/argv register setup in init7.S. */
uint16_t mlk_argv_base;

static int uart_putchar(char c, FILE *stream)
{
  (void)stream;
  loop_until_bit_is_set(UCSR0A, UDRE0);
  UDR0 = (unsigned char)c;
  return 0;
}

/* Set up stdout stream for avr-libc printf */
static FILE mystdout = FDEV_SETUP_STREAM(uart_putchar, NULL, _FDEV_SETUP_WRITE);

/* Init6 function - copy argc/argv block from EEPROM to top of RAM and
 * point the stack just below it. The scratch stack above RAM_TOP is used
 * for the eeprom_read_* calls; the default stack location (RAMEND of the
 * unpatched MCU) may lie inside .data/.bss and must not be used. */
void setup_args(void) __attribute__((naked, section(".init6"), used));
void setup_args(void)
{
  uint16_t base;
  SPH = 0xFF;
  SPL = 0xFF;
  base = eeprom_read_word((const uint16_t *)0);
  eeprom_read_block((void *)base, (const void *)2, (size_t)(RAM_TOP - base));
  mlk_argv_base = base;
  base--;
  SPH = (uint8_t)(base >> 8);
  SPL = (uint8_t)(base & 0xFF);
}

/* This is run as part of the init sequence, after setting up the stack
 * but before calling `main`. We mark it as naked but don't provide a return
 * instruction, so it is effectively inlined into the startup code. */
void setup_stdout(void) __attribute__((naked, section(".init7"), used));
/* Wire both stdout and stderr to the UART. The tests' CHECK(...) macros report
 * failures via fprintf(stderr, ...); without this, stderr is NULL and those
 * "ERROR (file,line)" lines would never reach simavr. */
void setup_stdout(void) { stdout = stderr = &mystdout; }

/* Override avr-libc exit(): pass the exit code to simavr. Called with the
 * return value of main() after main() returns. */
void exit(int code)
{
  cli();
  GPIOR0 = (code == 0) ? SIMAVR_CMD_EXIT_CODE_0 : SIMAVR_CMD_EXIT_CODE_1;
  /* Fallback in case the exit-code command is not supported */
  sleep_cpu();
  for (;;)
    ;
}

/* Called on UBSan traps (-fsanitize-trap). The avr-libc default would
 * stop simavr without any output, hiding the failure. */
void abort(void)
{
  printf("ERROR: abort() called (e.g. UBSan trap)\n");
  exit(1);
}
