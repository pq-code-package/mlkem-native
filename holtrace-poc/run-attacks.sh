#!/usr/bin/env bash
# Copyright (c) The mlkem-native project authors
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
#
# TEMPORARY PoC: run each attack in holtrace-poc/attacks/ twice.
#
# 1. As the current CI does: build-proof.sh + the success check from
#    proofs/hol_light/aarch64/Makefile (no "error:"/"exception:" in the
#    log, and "Running time:" present).
# 2. Under HOLTrace, then replay the trace with restore-trace.sh.
#
# Usage (inside `nix develop .#hol_light`):
#   HOLTRACE_HOL=<HOL Light dir with holtrace.ml installed> \
#   OUT=<output dir> holtrace-poc/run-attacks.sh [attack.ml ...]

set -uo pipefail

POC=$(cd "$(dirname "$0")" && pwd)
OUT=${OUT:-/tmp/holtrace-poc/out}
mkdir -p "$OUT"
OUT=$(cd "$OUT" && pwd)

if [[ $# == 0 ]]; then
  set -- "$POC"/attacks/*.ml
fi

for attack in "$@"; do
  attack=$(cd "$(dirname "$attack")" && pwd)/$(basename "$attack")
  tag=$(basename "$attack" .ml)
  echo "=== $tag"

  # (1) Current CI check, with the stock nix HOL Light
  "$POC/../proofs/hol_light/aarch64/proofs/build-proof.sh" "$attack" \
    "$HOLLIGHT_DIR/hol.sh" "$OUT/$tag.base.native" >/dev/null
  (cd "$POC/../proofs/hol_light" && "$OUT/$tag.base.native" >"$OUT/$tag.base.log" 2>&1)
  rm -f "$OUT/$tag.base.native"
  grep "Proof process shows" "$OUT/$tag.base.log"
  if grep -i "error:\|exception:" "$OUT/$tag.base.log" >/dev/null; then
    echo "CI check: FAIL (errors)"
  elif ! grep -q "Running time:" "$OUT/$tag.base.log"; then
    echo "CI check: FAIL (did not complete)"
  else
    echo "CI check: OK"
  fi

  # (2) HOLTrace: record, then replay in a clean process
  OUT=$OUT "$POC/trace-proof.sh" aarch64 mlkem_poly_reduce_aarch64_asm "$attack" >/dev/null ||
    echo "trace run failed"
  if "$POC/restore-trace.sh" "$OUT/$tag.50" "$OUT/$tag.thms" >"$OUT/$tag.restore.summary"; then
    echo "HOLTrace replay: ACCEPTED"
  else
    echo "HOLTrace replay: REJECTED"
  fi
  grep -E "RESTORED|Failure|Assert|refusing|exception" "$OUT/$tag.restore.summary" "$OUT/$tag.restore.log" 2>/dev/null |
    sed 's/^[^:]*://' | sort -u | head -5
  grep -A3 "^RESTORED" "$OUT/$tag.restore.log" 2>/dev/null
done
