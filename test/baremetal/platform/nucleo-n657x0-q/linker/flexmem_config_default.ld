/*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */

/* Cortex-M55 GCC linker script:
 * SRAM: 64 KiB  @ 0x00000000
 * DTCM: 128 KiB @ 0x30000000
 */

ENTRY(Reset_Handler)

MEMORY
{
  SRAM (rx)  : ORIGIN = 0x34064000, LENGTH = 64K
  DTCM (rwx) : ORIGIN = 0x30000000, LENGTH = 128K
}

__sram_start__ = ORIGIN(SRAM);
__sram_size__  = LENGTH(SRAM);
__dtcm_start__ = ORIGIN(DTCM);
__dtcm_size__  = LENGTH(DTCM);

__stack_size__ = 64K;
__heap_size__  = 0;

__StackTop   = ORIGIN(DTCM) + LENGTH(DTCM);
__StackLimit = __StackTop - __stack_size__;

PROVIDE(__stack = __StackTop);
PROVIDE(_estack = __StackTop);
PROVIDE(__initial_sp = __StackTop);
PROVIDE(_sstack = __StackLimit);

SECTIONS
{
  .vectors ORIGIN(SRAM) :
  {
    KEEP(*(.isr_vector))
    KEEP(*(.vectors))
    . = ORIGIN(SRAM) + 0x400;
  } > SRAM

  .text :
  {
    . = ALIGN(4);
    __text_start__ = .;

    *(.text)
    *(.text.*)
    *(.gnu.linkonce.t.*)

    KEEP(*(.init))
    KEEP(*(.fini))

    *(.rodata)
    *(.rodata.*)
    *(.gnu.linkonce.r.*)

    . = ALIGN(4);
    KEEP(*(.eh_frame*))
    KEEP(*(.ARM.extab* .gnu.linkonce.armextab.*))

    . = ALIGN(4);
    __exidx_start = .;
    KEEP(*(.ARM.exidx* .gnu.linkonce.armexidx.*))
    __exidx_end = .;

    . = ALIGN(4);
    __text_end__ = .;
  } > SRAM

  .gnu.sgstubs :
  {
    . = ALIGN(32);
    KEEP(*(.gnu.sgstubs))
    KEEP(*(.gnu.sgstubs.*))
    . = ALIGN(32);
  } > SRAM

  .preinit_array :
  {
    PROVIDE_HIDDEN(__preinit_array_start = .);
    KEEP(*(.preinit_array*))
    PROVIDE_HIDDEN(__preinit_array_end = .);
  } > SRAM

  .init_array :
  {
    PROVIDE_HIDDEN(__init_array_start = .);
    KEEP(*(SORT(.init_array.*)))
    KEEP(*(.init_array*))
    PROVIDE_HIDDEN(__init_array_end = .);
  } > SRAM

  .fini_array :
  {
    PROVIDE_HIDDEN(__fini_array_start = .);
    KEEP(*(SORT(.fini_array.*)))
    KEEP(*(.fini_array*))
    PROVIDE_HIDDEN(__fini_array_end = .);
  } > SRAM

  __etext = ALIGN(4);
  _etext  = __etext;

  .data : AT(__etext)
  {
    . = ALIGN(4);
    __data_start__ = .;
    _sdata = .;

    *(.data)
    *(.data.*)
    *(.gnu.linkonce.d.*)

    . = ALIGN(4);
    __data_end__ = .;
    _edata = .;
  } > DTCM

  __data_load__ = LOADADDR(.data);
  _sidata = __data_load__;

  .bss (NOLOAD) :
  {
    . = ALIGN(4);
    __bss_start__ = .;
    _sbss = .;

    *(.bss)
    *(.bss.*)
    *(.gnu.linkonce.b.*)
    *(COMMON)

    . = ALIGN(4);
    __bss_end__ = .;
    _ebss = .;
  } > DTCM

  .heap (NOLOAD) :
  {
    . = ALIGN(8);
    __end__ = .;
    end = .;
    _end = .;
    __HeapBase = .;
    . += __heap_size__;
    . = ALIGN(8);
  } > DTCM

  __HeapLimit = __StackLimit;

  .stack __StackLimit (NOLOAD) :
  {
    . = ALIGN(8);
    _sstack = .;
    . += __stack_size__;
  } > DTCM

  /DISCARD/ :
  {
    *(.note*)
    *(.comment*)
  }
}

ASSERT(SIZEOF(.vectors) <= 0x400, "Vector table exceeds 0x400 bytes")
ASSERT(__StackLimit >= __HeapBase, "DTCM overflow: data/bss/heap collide with stack")
ASSERT(__text_end__ <= ORIGIN(SRAM) + LENGTH(SRAM), "SRAM overflow")
ASSERT(__StackTop == ORIGIN(DTCM) + LENGTH(DTCM), "Bad stack top")
