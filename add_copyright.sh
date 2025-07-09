#!/bin/bash

# Find all Makefiles tracked by git
files=$(git ls-files -s | grep "^100" | cut -f2 | grep "Makefile$")

for f in $files; do
    echo "Processing: $f"
    perl -pi -e '
        # First pass: add copyright line if not present and SPDX exists
        $spdx = 1 if /^# SPDX-License-Identifier: Apache-2\.0$/;
        if ($. == 1 && $spdx && !/^# Copyright/) {
            $_ = "# Copyright (c) The mlkem-native project authors\n" . $_;
        }
        # Second pass: modify SPDX line
        s|^# SPDX-License-Identifier: Apache-2\.0$|# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT|;
    ' "$f"
done
