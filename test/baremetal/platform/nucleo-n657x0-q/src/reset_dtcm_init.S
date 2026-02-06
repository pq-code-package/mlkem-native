/*
 * DTCM sizing + MSP/MSPLIM bootstrap for NUCLEO-N657X0-Q (Cortex-M55)
 * - Checks SYSCFG_CM55TCMCR lower 8 bits; if not 0x99, writes 0x99 and resets via AIRCR
 * - Else sets MSP to 0x30040000 and MSPLIM to 0x30000000 before any C stack usage
 * - Injected into Reset_Handler via --wrap=Reset_Handler
 */

    .syntax unified
    .thumb

    .global __wrap_SystemInit
    .type __wrap_SystemInit, %function
    .extern __real_SystemInit

/* Constants */
#define SYSCFG_BASE      0x46008000
#define SYSCFG_CM55TCMCR 0x00000008  /* offset from SYSCFG_BASE */
/* RCC APB4ENSR2 address and bit for SYSCFGENS (enable) from device header:
 *   RCC_BASE_S = PERIPH_BASE_S(0x50000000) + AHB4PERIPH(0x06020000) + 0x8000 = 0x56028000
 *   APB4ENSR2 offset = 0x0A78 => 0x56028A78
 *   SYSCFGENS bit = 1<<0
 */
#define RCC_APB4ENSR2_ADDR 0x46028A78

#define SCB_AIRCR_ADDR   0xE000ED0C
#define AIRCR_SYSRESET   0x05FA0004  /* VECTKEY(0x05FA)<<16 | SYSRESETREQ */

#define DTCM_BASE        0x30000000
#define DTCM_SIZE_256K   0x00040000

/*
 * Wrap SystemInit to apply/check TCM sizing and set MSP/MSPLIM into DTCM
 * before any C stack use within SystemInit or later code.
 */
__wrap_SystemInit:
    /* Ensure SYSCFG clock is enabled before touching TCMCR */
    ldr   r0, =RCC_APB4ENSR2_ADDR
    ldr   r1, [r0]
    orr   r1, r1, #1
    str   r1, [r0]

    /* Read SYSCFG_CM55TCMCR */
    ldr   r0, =SYSCFG_BASE
    ldr   r1, =SYSCFG_CM55TCMCR
    add   r0, r0, r1
    ldr   r1, [r0]
    /* Mask lower 8 bits and compare to 0x99 */
    movs  r0, #0xFF
    ands  r1, r1, r0
    cmp   r1, #0x99
    beq   2f

    /* Not 0x99: write 0x99 into lower byte of SYSCFG_CM55TCMCR */
    /* Reload address */
    ldr   r0, =SYSCFG_BASE
    ldr   r1, =SYSCFG_CM55TCMCR
    add   r0, r0, r1
    /* Read-modify-write to update only the low byte */
    ldr   r1, [r0]
    bic   r1, r1, #0xFF
    orr   r1, r1, #0x99
    str   r1, [r0]

    /* Trigger system reset via AIRCR */
    ldr   r0, =SCB_AIRCR_ADDR
    ldr   r1, =AIRCR_SYSRESET
    str   r1, [r0]
1:  b     1b

2:
    /* Correct sizing: set MSP = DTCM_BASE + 256K, MSPLIM = DTCM_BASE */
    ldr   r0, =DTCM_BASE
    ldr   r1, =DTCM_SIZE_256K
    add   r0, r0, r1
    msr   MSP, r0
    ldr   r0, =DTCM_BASE
    msr   MSPLIM, r0

    /* Tail-call real SystemInit */
    b     __real_SystemInit
