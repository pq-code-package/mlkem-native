#!/bin/bash

# Find all .md files tracked by git
files=$(git ls-files -s | grep "^100" | cut -f2 | grep "\.md$")

for f in $files; do
    echo "Processing: $f"
    perl -pi -e '
        # Enable multiline matching
        BEGIN { undef $/; }
        # Replace the header and ensure exactly one blank line after
        s|^\[//\]: # \(SPDX-License-Identifier: CC-BY-4\.0\)\n*|[//]: # (Copyright (c) The mlkem-native project authors)\n[//]: # (SPDX-License-Identifier: Apache-2.0)\n\n|;
    ' "$f"
done
