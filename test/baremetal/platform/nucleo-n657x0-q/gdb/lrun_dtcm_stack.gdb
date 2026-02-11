# LRUN DTCM sizing and stack placement helper for STM32N657 (Cortex-M55)
# - Enables SYSCFG clock
# - Ensures SYSCFG_CM55TCMCR low byte is 0x99 (256 KiB D-TCM) and resets once if changed
# - Startup will load initial SP from the vector table; LRUN linker is patched to place it in D-TCM

set pagination off
set confirm off

# Expect target already connected (target remote) before sourcing this file.

# RCC APB4ENSR2 (enable SYSCFG): 0x46028A78, bit 0
set *0x46028A78=1

# SYSCFG base 0x46008000; CM55TCMCR offset 0x08; low byte selects D-TCM size (0x99 -> 256 KiB)
set *(unsigned int*)0x46008008 = 0x99
monitor reset

