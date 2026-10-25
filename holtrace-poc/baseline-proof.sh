#!/usr/bin/env bash
# Copyright (c) The mlkem-native project authors
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
#
# TEMPORARY PoC: run one proof with the stock (nix) HOL Light, to get a
# time/memory baseline for comparison with trace-proof.sh.
#
# Usage (inside `nix develop .#hol_light`):
#   OUT=<output dir> holtrace-poc/baseline-proof.sh <arch> <proof basename>

set -euo pipefail

arch=$1
name=$2
POC=$(cd "$(dirname "$0")" && pwd)
ROOT=$(git -C "$POC" rev-parse --show-toplevel)
OUT=${OUT:-/tmp/holtrace-poc/out}
mkdir -p "$OUT"
OUT=$(cd "$OUT" && pwd)

make -C "$ROOT/proofs/hol_light/$arch" "mlkem/$name.o"
"$ROOT/proofs/hol_light/$arch/proofs/build-proof.sh" \
  "$ROOT/proofs/hol_light/$arch/proofs/$name.ml" "$HOLLIGHT_DIR/hol.sh" "$OUT/$name.base.native"
cd "$ROOT/proofs/hol_light"
/usr/bin/time -l "$OUT/$name.base.native" >"$OUT/$name.base.log" 2>&1
rm -f "$OUT/$name.base.native"
grep -E "Running time|real|maximum resident" "$OUT/$name.base.log" || true
