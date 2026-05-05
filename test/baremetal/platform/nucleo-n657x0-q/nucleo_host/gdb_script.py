# Copyright (c) The mlkem-native project authors
# Copyright (c) Arm Ltd.
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

"""Generate the GDB batch script used to load and run RAM-resident tests."""


def build_run_script(
    *,
    port,
    wrap_main_break,
    reset_handler_jump,
    argv_bin,
    arg_block_addr,
    arg_block_sym,
    stdout_capture_addr,
    stdout_capture_len_addr,
    stdout_capture_truncated_addr,
    stdout_capture_size,
    stdout_capture_bin,
):
    """
    Build the full GDB command list for one test-image run.

    The order is part of the platform contract: load the RAM ELF, run normal
    C startup until ``__wrap_main``, restore argv after ``.bss`` has been
    cleared, install target-failure breakpoints, continue, then harvest stdout
    and fault diagnostics after execution stops.
    """
    gdb_lines = [
        "set pagination off",
        "set confirm off",
        f"target remote localhost:{port}",
        # Semihosting is configured on the ST-LINK GDB server command line; the
        # GDB script stays focused on target state and RAM transfers.
        "load",
        f"tbreak {wrap_main_break}",
        f"jump {reset_handler_jump}",
        restore_argv_command(argv_bin, arg_block_addr, arg_block_sym),
        "break HardFault_Handler",
        "commands",
        "  echo [[NUCLEO-HARDFAULT]]\\n",
        "end",
        "break nucleo_layout_fail",
        "commands",
        "  echo [[NUCLEO-LAYOUT-FAIL]]\\n",
        "end",
        "continue",
    ]
    if stdout_capture_addr and stdout_capture_len_addr:
        gdb_lines += stdout_capture_dump_commands(
            stdout_capture_addr=stdout_capture_addr,
            stdout_capture_len_addr=stdout_capture_len_addr,
            stdout_capture_size=stdout_capture_size,
            stdout_capture_bin=stdout_capture_bin,
        )
    if stdout_capture_truncated_addr:
        gdb_lines += [
            "set $nucleo_stdout_truncated = *(unsigned int *)"
            f"{stdout_capture_truncated_addr}",
            "p/x $nucleo_stdout_truncated",
        ]
    gdb_lines += fault_diagnostic_commands()
    return gdb_lines


def restore_argv_command(argv_bin, arg_block_addr, arg_block_sym):
    """Return the GDB ``restore`` command for the packed argv blob."""
    if arg_block_addr:
        # Prefer a numeric address because some RAM-loaded ELFs have unreliable
        # symbol lookup after ``target remote``/``load`` transitions.
        return f"restore {argv_bin} binary {arg_block_addr}"
    return f"restore {argv_bin} binary &{arg_block_sym}"


def stdout_capture_dump_commands(
    *,
    stdout_capture_addr,
    stdout_capture_len_addr,
    stdout_capture_size,
    stdout_capture_bin,
):
    """Return commands that dump the target stdout capture buffer to a file."""
    return [
        f"set $nucleo_stdout_len = *(unsigned int *){stdout_capture_len_addr}",
        "if $nucleo_stdout_len > 0",
        # Clamp to the compile-time buffer size before using the
        # target-provided length as a host file dump bound.
        f"  if $nucleo_stdout_len > {stdout_capture_size}",
        f"    set $nucleo_stdout_len = {stdout_capture_size}",
        "  end",
        f"  dump binary memory {stdout_capture_bin} {stdout_capture_addr} "
        f"{stdout_capture_addr} + $nucleo_stdout_len",
        "end",
    ]


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
