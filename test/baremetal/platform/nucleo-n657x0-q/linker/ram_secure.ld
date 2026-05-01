/*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */

/* Cortex-M55 GCC linker script:
 * ITCM: 256 KiB @ 0x00000000
 * DTCM: 256 KiB @ 0x30000000
 */

ENTRY(Reset_Handler)

MEMORY
{
  ITCM (rwx) : ORIGIN = 0x00000000, LENGTH = 256K
  DTCM (rwx) : ORIGIN = 0x30000000, LENGTH = 256K
  AXISRAM (rwx) : ORIGIN = 0x34080000, LENGTH = 1536K
}

__itcm_start__ = ORIGIN(ITCM);
__itcm_size__  = LENGTH(ITCM);
__dtcm_start__ = ORIGIN(DTCM);
__dtcm_size__  = LENGTH(DTCM);

__stack_size__ = 192K;
__heap_size__  = 0;

__StackTop   = ORIGIN(DTCM) + LENGTH(DTCM);
__StackLimit = __StackTop - __stack_size__;
__HeapBase   = ORIGIN(DTCM);
__HeapLimit  = __StackLimit;

PROVIDE(__stack = __StackTop);
PROVIDE(_estack = __StackTop);
PROVIDE(__initial_sp = __StackTop);
PROVIDE(_sstack = __StackLimit);

SECTIONS
{
  .vectors ORIGIN(ITCM) :
  {
    KEEP(*(.isr_vector))
    KEEP(*(.vectors))
    . = ORIGIN(ITCM) + 0x400;
  } > ITCM

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
  } > ITCM

  .gnu.sgstubs :
  {
    . = ALIGN(32);
    KEEP(*(.gnu.sgstubs))
    KEEP(*(.gnu.sgstubs.*))
    . = ALIGN(32);
  } > ITCM

  .preinit_array :
  {
    PROVIDE_HIDDEN(__preinit_array_start = .);
    KEEP(*(.preinit_array*))
    PROVIDE_HIDDEN(__preinit_array_end = .);
  } > ITCM

  .init_array :
  {
    PROVIDE_HIDDEN(__init_array_start = .);
    KEEP(*(SORT(.init_array.*)))
    KEEP(*(.init_array*))
    PROVIDE_HIDDEN(__init_array_end = .);
  } > ITCM

  .fini_array :
  {
    PROVIDE_HIDDEN(__fini_array_start = .);
    KEEP(*(SORT(.fini_array.*)))
    KEEP(*(.fini_array*))
    PROVIDE_HIDDEN(__fini_array_end = .);
  } > ITCM
  
  .itcm_probe :
  {
    . = MAX(., ORIGIN(ITCM) + 0x00010000);
    . = ALIGN(32);
    KEEP(*(.itcm_probe))
    KEEP(*(.itcm_probe.*))
    . = ALIGN(32);
  } > ITCM

  .cmdline (NOLOAD) :
  {
    . = ALIGN(8);
    KEEP(*(.cmdline))
    KEEP(*(.cmdline.*))
    . = ALIGN(8);
    __itcm_end__ = .;
  } > ITCM

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

  .stdout_capture (NOLOAD) :
  {
    . = ALIGN(32);
    __stdout_capture_start__ = .;
    KEEP(*(.stdout_capture))
    KEEP(*(.stdout_capture.*))
    . = ALIGN(32);
    __stdout_capture_end__ = .;
  } > AXISRAM

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
ASSERT(__itcm_end__ <= ORIGIN(ITCM) + LENGTH(ITCM), "ITCM overflow")
ASSERT(__stdout_capture_end__ <= ORIGIN(AXISRAM) + LENGTH(AXISRAM), "AXISRAM overflow")
ASSERT(__StackTop == ORIGIN(DTCM) + LENGTH(DTCM), "Bad stack top")
