#!/bin/bash

files=$(git ls-files -s | grep "^100" | cut -f2)

for f in $files; do
    echo "Processing: $f"
    perl -pi -e '
        # Enable multiline matching
        BEGIN { undef $/; }
        # Look for the copyright line followed by SPDX line with any characters in between
        s|(Copyright \(c\) 2024-2025 The mlkem-native project authors.*?\n.*?SPDX-License-Identifier: Apache-2\.0)(.*?\n)|$1 OR ISC OR MIT$2|gs
    ' "$f"
done
