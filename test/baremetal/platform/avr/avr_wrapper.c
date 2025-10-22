/* Copyright (c) The mlkem-native project authors */
/* SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT */

#include <avr/eeprom.h>
#include <avr/interrupt.h>
#include <avr/io.h>
#include <avr/sleep.h>
#include <stdio.h>
#include <string.h>

#define RAM_BASE 0x2000

static int uart_putchar(char c, FILE *stream)
{
  (void)stream;
  loop_until_bit_is_set(UCSR0A, UDRE0);
  UDR0 = (unsigned char)c;
  return 0;
}

/* Set up stdout stream for avr-libc printf */
static FILE mystdout = FDEV_SETUP_STREAM(uart_putchar, NULL, _FDEV_SETUP_WRITE);

/* Init6 function - copy EEPROM to RAM */
void setup_args(void) __attribute__((naked, section(".init6"), used));
void setup_args(void)
{
  eeprom_read_block((void *)RAM_BASE, (void *)0x0000, 0x4000);
}

/* This is run as part of the init sequence, after setting up the stack
 * but before calling `main`. We mark it as naked but don't provide a return
 * instruction, so it is effectively inlined into the startup code. */
void setup_stdout(void) __attribute__((naked, section(".init7"), used));
void setup_stdout(void) { stdout = &mystdout; }

/* The above sequence makes simavr stop. */
void program_exit(void) __attribute__((section(".fini1"), used));
void program_exit(void)
{
  cli();
  sleep_cpu();
}
