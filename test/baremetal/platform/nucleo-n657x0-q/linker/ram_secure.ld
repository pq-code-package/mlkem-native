/* NUCLEO-N657X0-Q RAM-only Secure Linker Script
 * - Run from RAM only (no flash LMA)
 * - Secure mode only
 * - Stack in D-TCM:   0x30000000 .. 0x3003FFFF (MSP at 0x30040000)
 * - Hot code in I-TCM: 0x10000000 .. 0x1003FFFF
 * - Regular SRAM from  0x34064000 upward
 * - First 0x400 bytes of SRAM reserved for .isr_vector
 */

ENTRY(Reset_Handler)

/* Memory regions */
MEMORY
{
  ITCM (rx)  : ORIGIN = 0x00000000, LENGTH = 0x00040000
  DTCM (rwx) : ORIGIN = 0x20000000, LENGTH = 0x00040000
  VECT (rx)  : ORIGIN = 0x34064000, LENGTH = 0x00000400 /* reserved for .isr_vector */
  SRAM (rwx) : ORIGIN = 0x34064400, LENGTH = 0x00FFFC00 /* remainder of SRAM window */
}

/* Explicit program headers to avoid orphaned sections */
PHDRS
{
  itcm_text PT_LOAD FLAGS(5);   /* R X */
  sram_rw   PT_LOAD FLAGS(7);   /* R W X (single segment for simplicity) */
}

/* Stack in D-TCM: use top of region */
PROVIDE(_estack = ORIGIN(DTCM) + LENGTH(DTCM));
PROVIDE(__StackTop = _estack);
PROVIDE(__initial_sp = _estack);
PROVIDE(__StackLimit = ORIGIN(DTCM));
PROVIDE(_sstack = __StackLimit);

/* Optional heap/stack minima (not enforced) */
_Min_Heap_Size  = 0x0000;
_Min_Stack_Size = 0x0000;

/* Section placement */
SECTIONS
{
  /* Vector table region (0x34064000..0x340643FF) */
  .isr_vector :
  {
    . = ALIGN(4);
    KEEP(*(.isr_vector))
    KEEP(*(.isr_vector.*))
    . = ALIGN(4);
  } > VECT :sram_rw

  /* High-speed code in I-TCM (optional) */
  .itcm_text :
  {
    . = ALIGN(8);
    KEEP(*(.itcm_text))
    *(.itcm_text.*)
    *(.text.itcm)
    *(.text.itcm.*)
    *(.ramfunc.itcm)
    *(.ramfunc.itcm.*)
    . = ALIGN(8);
  } > ITCM :itcm_text

  /* Regular code in SRAM */
  .text :
  {
    . = ALIGN(8);
    KEEP(*(.text.startup))
    *(.text)
    *(.text.*)
    KEEP(*(.init))
    KEEP(*(.fini))
    . = ALIGN(8);
  } > SRAM :sram_rw

  /* CMSE veneers/stubs (secure gateway) must be in executable region */
  .gnu.sgstubs :
  {
    . = ALIGN(4);
    KEEP(*(.gnu.sgstubs))
    . = ALIGN(4);
  } > SRAM :sram_rw

  /* Exception unwinding tables */
  .ARM.extab :
  {
    *(.ARM.extab* .gnu.linkonce.armextab.*)
  } > SRAM :sram_rw

  __exidx_start = .;
  .ARM.exidx :
  {
    *(.ARM)
    *(.ARM.exidx* .gnu.linkonce.armexidx.*)
  } > SRAM :sram_rw
  __exidx_end = .;

  /* Read-only data */
  .rodata :
  {
    . = ALIGN(32);
    *(.rodata)
    *(.rodata.*)
    . = ALIGN(32);
  } > SRAM :sram_rw

  /* C++ init/fini arrays */
  .preinit_array :
  {
    PROVIDE(__preinit_array_start = .);
    KEEP(*(.preinit_array*))
    PROVIDE(__preinit_array_end = .);
  } > SRAM :sram_rw

  .init_array :
  {
    PROVIDE(__init_array_start = .);
    KEEP(*(SORT_BY_INIT_PRIORITY(.init_array.*)))
    KEEP(*(.init_array*))
    PROVIDE(__init_array_end = .);
  } > SRAM :sram_rw

  .fini_array :
  {
    PROVIDE(__fini_array_start = .);
    KEEP(*(SORT_BY_INIT_PRIORITY(.fini_array.*)))
    KEEP(*(.fini_array*))
    PROVIDE(__fini_array_end = .);
  } > SRAM :sram_rw

  /* Writable data (no flash LMA; RAM-run) */
  _sidata = .;
  .data :
  {
    . = ALIGN(8);
    _sdata = .;
    *(.data)
    *(.data.*)
    *(.data.rel.ro*)
    . = ALIGN(8);
    _edata = .;
  } > SRAM :sram_rw

  /* Optional noncacheable (default to SRAM) */
  .noncacheable (NOLOAD) :
  {
    *(.noncacheable)
    *(.noncacheable.*)
  } > SRAM :sram_rw

  /* Zero-initialized data */
  .bss (NOLOAD) :
  {
    . = ALIGN(8);
    _sbss = .;
    *(.bss)
    *(.bss.*)
    *(COMMON)
    . = ALIGN(8);
    _ebss = .;
  } > SRAM :sram_rw
  PROVIDE(end = _ebss);

  /* Vendor placeholder (do not use for stack) */
  ._user_heap_stack (NOLOAD) :
  {
    *(._user_heap_stack*)
  } > SRAM :sram_rw

  /* Discard non-allocated/debug sections */
  /DISCARD/ :
  {
    *(.comment)
    *(.note*)
    *(.gnu_debuglink)
    *(.gnu.lto_*)
    *(.ARM.attributes)
    *(.debug*)
  }
}
