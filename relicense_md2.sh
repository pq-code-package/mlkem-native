#!/bin/bash

# Find all .md files tracked by git
files=$(git ls-files -s | grep "^100" | cut -f2 | grep "\.md$")

for f in $files; do
    echo "Processing: $f"
    perl -pi -e '
        s|SPDX-License-Identifier: Apache-2\.0 OR ISC OR MIT|SPDX-License-Identifier: CC-BY-4.0|g;
    ' "$f"
done
