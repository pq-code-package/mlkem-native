#!@bash@
# Copyright (c) The mlkem-native project authors
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
# shellcheck shell=bash disable=SC2239

set -eu

# Use a temporary 64 GiB heap budget instead of scaling with trace size.
# CakeML reads this capacity in MiB; hol-trace separately measures peak RSS.
export CML_HEAP_SIZE="${CML_HEAP_SIZE:-65536}"

echo "candle-holtrace: heap capacity ${CML_HEAP_SIZE} MiB; stack capacity ${CML_STACK_SIZE-1024} MiB" >&2

cd @candle@/candle/build
exec ./cake --candle \
  "$HOLTRACE_TRACE" "$HOLTRACE_NAMES" "$HOLTRACE_RESULT" \
  <../run-holtrace.ml
