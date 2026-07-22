#!/usr/bin/env python3
# Copyright (c) The mlkem-native project authors
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

import sys
import subprocess
import os
import tempfile

# The argc/argv block is placed at the top of RAM, just below 16 bytes of
# scratch stack used during startup (see avr_wrapper.c). The stack grows
# downwards from just below the block.
RAM_TOP = 0xFFF0

# Patched EEPROM size (see nix/avr/simavr-32k-eeprom.patch)
EEPROM_SIZE = 0x8000


def intel_hex_line(addr, data):
    """Generate Intel HEX format line"""
    record_type = 0
    count = len(data)
    line = f":{count:02X}{addr:04X}{record_type:02X}"
    checksum = count + (addr >> 8) + (addr & 0xFF) + record_type
    for b in data:
        line += f"{b:02X}"
        checksum += b
    checksum = (-checksum) & 0xFF
    line += f"{checksum:02X}"
    return line


def create_eeprom_hex(args, output_file):
    """
    Create EEPROM hex file from command line arguments.

    EEPROM layout: 2 bytes block base address (little-endian), followed by
    the argc/argv block to be copied to that address:
    argc (2 bytes) + argv array (len(args) * 2 bytes) + packed strings.
    """
    # First arg should be binary name (strip path)
    args = [os.path.basename(args[0])] + args[1:]

    # Step 1: Generate packed string data and record offsets
    strings_data = bytearray()
    string_offsets = []

    for arg in args:
        string_offsets.append(len(strings_data))
        strings_data.extend(arg.encode("utf-8"))
        strings_data.append(0x00)  # Null terminator

    # Step 2: Calculate where the block will be in RAM
    argc_size = 2
    argv_size = len(args) * 2
    block_size = argc_size + argv_size + len(strings_data)
    if block_size + 2 > EEPROM_SIZE:
        print(
            f"Error: argument block of {block_size} bytes does not fit in EEPROM",
            file=sys.stderr,
        )
        sys.exit(1)
    base = RAM_TOP - block_size
    strings_ram_base = base + argc_size + argv_size

    # Step 3: Build EEPROM data: block base address, then argc
    data = bytearray()
    data.extend([base & 0xFF, (base >> 8) & 0xFF])
    data.extend([len(args) & 0xFF, (len(args) >> 8) & 0xFF])

    # Step 4: Build argv array with pointers to RAM addresses
    for offset in string_offsets:
        ptr = strings_ram_base + offset
        data.extend([ptr & 0xFF, (ptr >> 8) & 0xFF])  # Little-endian

    # Step 5: Append packed strings
    data.extend(strings_data)

    output = []

    # Write Intel HEX file
    # Extended Linear Address for EEPROM (0x810000)
    output.append(":02000004008179")

    # Write data in 16-byte chunks
    for i in range(0, len(data), 16):
        chunk = data[i : i + 16]
        output.append(intel_hex_line(i, chunk))

    # End of file
    output.append(":00000001FF")

    with open(output_file, "w+") as f:
        f.write("\n".join(output))


def main():
    if len(sys.argv) < 2:
        print("Usage: exec_wrapper.py <elf_file> [args...]", file=sys.stderr)
        sys.exit(1)

    elf_file = sys.argv[1]

    # Check if file exists
    if not os.path.exists(elf_file):
        print(f"Error: {elf_file} not found", file=sys.stderr)
        sys.exit(1)

    # Create temporary EEPROM hex file from command line arguments
    with tempfile.NamedTemporaryFile(mode="w", suffix=".hex", delete=False) as tmp:
        eeprom_file = tmp.name

    try:
        # Generate EEPROM with argv
        create_eeprom_hex(sys.argv[1:], eeprom_file)

        # Run with simavr - enable UART output
        # Note that we use a patched version of simavr where atmega128rfr2
        # has 63.5K of RAM. This is purely for testing purposes.
        cmd = [
            "simavr",
            "-m",
            "atmega128rfr2",
            "-f",
            "16000000",
            "-v",
            elf_file,
            "-ee",
            eeprom_file,
        ]

        result = subprocess.run(cmd, capture_output=True, text=True, timeout=300)

        # Somehow, the output ends up on stderr
        output = ""
        if result.stderr:
            import re

            # Filter out "Load" lines and ANSI color codes from stderr
            lines = result.stderr.split("\n")
            filtered_lines = []
            for line in lines:
                if not line.startswith("Load"):
                    # Remove ANSI color codes
                    clean_line = re.sub(r"\x1b\[[0-9;]*m", "", line)
                    filtered_lines.append(clean_line)
            output = "\n".join(filtered_lines)

        # The guest exit code is propagated via simavr's exit-code commands
        # (see avr_wrapper.c). As an additional safety net, scan the output
        # for "ERROR" and fail: this catches failures where the firmware
        # stops without reaching exit(), and both the UBSan-trap abort() in
        # avr_wrapper.c and the CHECK(...) macros in the tests print
        # "ERROR (file,line)" on failure.
        #
        # On failure, write to stderr, otherwise stdout.
        if "ERROR" in output:
            print(output, end="", file=sys.stderr)
            sys.exit(1)

        print(output, end="")
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

    finally:
        # Clean up temporary EEPROM file
        if os.path.exists(eeprom_file):
            os.unlink(eeprom_file)


if __name__ == "__main__":
    main()
