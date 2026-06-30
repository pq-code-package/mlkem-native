# Copyright (c) The mlkem-native project authors
# Copyright (c) Arm Ltd.
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

"""Generate the GDB batch script used to load and run RAM-resident tests."""


def build_run_script(
    *,
    port,
    wrap_main_break,
    reset_handler_jump,
    hardfault_break,
    done_break,
    argv_bin,
    arg_block_addr,
    arg_block_sym,
):
    """
    Build the full GDB command list for one test-image run.

    The order is part of the platform contract: load the RAM ELF, run normal
    C startup until ``__wrap_main``, restore argv after ``.bss`` has been
    cleared, install completion/fault breakpoints, continue, then read the
    target return code from the completion breakpoint.
    """
    gdb_lines = [
        "set pagination off",
        "set confirm off",
        f"target remote localhost:{port}",
        # Keep the GDB script focused on target state and RAM transfers.
        "load",
        f"tbreak {wrap_main_break}",
        f"jump {reset_handler_jump}",
        restore_argv_command(argv_bin, arg_block_addr, arg_block_sym),
        "set $nucleo_exit_code = -1",
        f"break {done_break}",
        "commands",
        "  set $nucleo_exit_code = $r0",
        "  echo [[NUCLEO-DONE]]\\n",
        "end",
        f"break {hardfault_break}",
        "commands",
        "  echo [[NUCLEO-HARDFAULT]]\\n",
        "end",
    ]
    gdb_lines += [
        "continue",
        "if $nucleo_exit_code != -1",
        "  echo NUCLEO_EXIT_CODE=",
        "  output/d $nucleo_exit_code",
        "  echo \\n",
        "end",
    ]
    gdb_lines += fault_diagnostic_commands()
    # Leave the board in a fresh boot state for the next FLEXMEM setup. This
    # runs after stdout/fault harvesting and does not affect the current test.
    gdb_lines += ["monitor reset_config none", "monitor reset run"]
    return gdb_lines


def restore_argv_command(argv_bin, arg_block_addr, arg_block_sym):
    """Return the GDB ``restore`` command for the packed argv blob."""
    if arg_block_addr:
        # Prefer a numeric address because some RAM-loaded ELFs have unreliable
        # symbol lookup after ``target remote``/``load`` transitions.
        return f"restore {argv_bin} binary {arg_block_addr}"
    return f"restore {argv_bin} binary &{arg_block_sym}"


def fault_diagnostic_commands():
    """Return commands that print Cortex-M fault diagnostics."""
    return [
        "info registers",
        "x/4wx $sp",
        "echo CFSR=",
        "output/x *(unsigned int *)0xE000ED28",
        "echo \\n",
        "echo HFSR=",
        "output/x *(unsigned int *)0xE000ED2C",
        "echo \\n",
        "echo DFSR=",
        "output/x *(unsigned int *)0xE000ED30",
        "echo \\n",
        "echo MMFAR=",
        "output/x *(unsigned int *)0xE000ED34",
        "echo \\n",
        "echo BFAR=",
        "output/x *(unsigned int *)0xE000ED38",
        "echo \\n",
        "echo AFSR=",
        "output/x *(unsigned int *)0xE000ED3C",
        "echo \\n",
        "echo SHCSR=",
        "output/x *(unsigned int *)0xE000ED24",
        "echo \\n",
        "echo CCR=",
        "output/x *(unsigned int *)0xE000ED14",
        "echo \\n",
        "echo MSP=",
        "output/x $msp",
        "echo \\n",
        "echo PSP=",
        "output/x $psp",
        "echo \\n",
        "echo LR=",
        "output/x $lr",
        "echo \\n",
        "echo PC=",
        "output/x $pc",
        "echo \\n",
        "echo STACKED_R0_R1_R2_R3_R12_LR_PC_XPSR:\\n",
        "if ($lr & 4)",
        "  x/8wx $psp",
        "else",
        "  x/8wx $msp",
        "end",
        "x/4wx 0xE000ED28",
        "x/wx 0xE000ED38",
    ]
