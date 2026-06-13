# Copyright (c) The mlkem-native project authors
# Copyright (c) Arm Ltd.
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

"""User-facing helpers for NUCLEO FLEXMEM configuration."""

PLATFORM_MK = "test/baremetal/platform/nucleo-n657x0-q/platform.mk"


def flexmem_config_build_instructions(config_elf: str) -> str:
    """Return instructions for generating a missing FLEXMEM config ELF."""
    return "\n".join(
        [
            "Build the FLEXMEM config ELF from the repository root with:",
            f"  make flexmem_config EXTRA_MAKEFILE={PLATFORM_MK}",
            "Then configure the board with:",
            f"  make run_flexmem_config EXTRA_MAKEFILE={PLATFORM_MK}",
            "If you override BUILD_DIR or FLEXMEM_CONFIG_ELF, pass the "
            "same override to the make command.",
            f"Expected FLEXMEM config ELF: {config_elf}",
        ]
    )
