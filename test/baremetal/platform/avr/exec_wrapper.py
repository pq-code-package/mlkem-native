#!/usr/bin/env python3
# Copyright (c) The mlkem-native project authors
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

import sys
import subprocess
import os


def main():
    if len(sys.argv) < 2:
        print("Usage: exec_wrapper.py <elf_file>", file=sys.stderr)
        sys.exit(1)

    elf_file = sys.argv[1]

    # Check if file exists
    if not os.path.exists(elf_file):
        print(f"Error: {elf_file} not found", file=sys.stderr)
        sys.exit(1)

    # Run with simavr - enable UART output
    try:
        # -m atmega128rfr2: MCU type
        # -f 16000000: frequency
        # -v: verbose mode to see UART output
        #
        # Note that we use a patched version of simavr where atmega128rfr2
        # has 32K of RAM. This is purely for testing purposes. If/Once the
        # library has [an option for] reduced stack usage, we may be able
        # to use the standard MCU model. The primary purpose of this test,
        # at the moment, is less to demonstrate that mlkem-native is ready
        # yet for usage on MCUs, but to confirm that, functionally, nothing
        # in the library depends on int being 32-bit wide.
        cmd = ["simavr", "-m", "atmega128rfr2", "-f", "16000000", "-v", elf_file]

        result = subprocess.run(cmd, capture_output=True, text=True, timeout=300)

        # Somehow, the output ends up on stderr
        if result.stderr:
            import re

            # Filter out "Loaded" lines and ANSI color codes from stderr
            lines = result.stderr.split("\n")
            filtered_lines = []
            for line in lines:
                if not line.startswith("Loaded "):
                    # Remove ANSI color codes
                    clean_line = re.sub(r"\x1b\[[0-9;]*m", "", line)
                    filtered_lines.append(clean_line)
            print("\n".join(filtered_lines), end="")

        sys.exit(result.returncode)

    except subprocess.TimeoutExpired:
        print("Error: Simulation timed out after 300 seconds", file=sys.stderr)
        sys.exit(1)
    except FileNotFoundError:
        print("Error: simavr not found. Make sure it's in PATH", file=sys.stderr)
        sys.exit(1)
    except Exception as e:
        print(f"Error running simulation: {e}", file=sys.stderr)
        sys.exit(1)


if __name__ == "__main__":
    main()
