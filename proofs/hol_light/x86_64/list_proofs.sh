#!/usr/bin/env bash
# Copyright (c) The mlkem-native project authors
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
#
# This tiny script just lists the names of source files for which
# we have a spec and proof in HOL-Light.

set -euo pipefail
cd "$(dirname "$(realpath "$0")")/mlkem"
ls -1 -- *.S | sed 's/\.S$//'
