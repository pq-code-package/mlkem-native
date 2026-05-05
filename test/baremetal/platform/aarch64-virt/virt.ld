/*
 * Copyright (c) The mldsa-native project authors
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */

/*
 * Linker script for AArch64 QEMU virt machine.
 * RAM starts at 0x40000000 (QEMU virt default).
 */

ENTRY(_start)

MEMORY
{
    RAM (rwx) : ORIGIN = 0x40000000, LENGTH = 128M
}

SECTIONS
{
    .text : ALIGN(4096)
    {
        *(.text.vectors)
        *(.text.start)
        *(.text*)
    } > RAM

    .rodata : ALIGN(16)
    {
        *(.rodata*)
    } > RAM

    .data : ALIGN(16)
    {
        *(.data*)
    } > RAM

    .bss (NOLOAD) : ALIGN(16)
    {
        __bss_start = .;
        __bss_start__ = .;
        *(.bss*)
        *(COMMON)
        __bss_end = .;
        __bss_end__ = .;
    } > RAM

    end = .;
    __end__ = .;

    /* Heap grows upward from end toward stack */
    .heap (NOLOAD) : ALIGN(16)
    {
        __heap_start = .;
        . += 16M;
        __heap_end = .;
    } > RAM

    /* 64 KB stack at the end */
    .stack (NOLOAD) : ALIGN(16)
    {
        __stack_bottom = .;
        . += 1M;
        __stack_top = .;
    } > RAM

    /* Small dedicated stack for exception handler */
    .exc_stack (NOLOAD) : ALIGN(16)
    {
        . += 4K;
        __exc_stack_top = .;
    } > RAM

    /DISCARD/ :
    {
        *(.comment)
        *(.note*)
        *(.eh_frame*)
        *(.ARM.*)
    }
}
