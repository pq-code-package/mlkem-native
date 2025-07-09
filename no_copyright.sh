#!/bin/bash

files=$(git ls-files -s | grep "^100" | cut -f2)

for f in $files; do
    perl -ne '
        BEGIN { $spdx = 0; $copyright = 0; }
        $spdx = 1 if /SPDX-License-Identifier:/;
        $copyright = 1 if /Copyright \(c\)/;
        END {
            print "$ARGV\n" if ($spdx && !$copyright);
        }
    ' "$f"
done
