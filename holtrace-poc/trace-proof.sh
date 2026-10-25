#!/usr/bin/env bash
# Copyright (c) The mlkem-native project authors
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
#
# TEMPORARY PoC: run one mlkem-native HOL Light proof under HOLTrace.
#
# Usage (inside `nix develop .#hol_light`):
#   HOLTRACE_HOL=<HOL Light dir with holtrace.ml installed> \
#   OUT=<output dir> \
#   holtrace-poc/trace-proof.sh <aarch64|x86_64> <proof basename> [proof .ml]
#
# The optional third argument replaces the proof script (used by the
# negative tests in holtrace-poc/attacks/). The object file is still
# taken from proofs/hol_light/<arch>/mlkem/<proof basename>.o.
#
# Produces in $OUT:
#   <name>.50          raw HOLTrace file
#   <name>.trace.log   proof output + /usr/bin/time -l statistics
#   <name>.thms        names of the theorems named in the trace

set -euo pipefail

arch=$1
name=$2
POC=$(cd "$(dirname "$0")" && pwd)
ROOT=$(git -C "$POC" rev-parse --show-toplevel)
HOLDIR=${HOLTRACE_HOL:?set HOLTRACE_HOL}
OUT=${OUT:-/tmp/holtrace-poc/out}
mkdir -p "$OUT"
OUT=$(cd "$OUT" && pwd)

# PROOF_SRC: tree with aarch64/, x86_64/, common/ (default: the real one;
# hashtt-prepare.sh makes a rewritten copy).
SRC=${PROOF_SRC:-$ROOT/proofs/hol_light}
proof=${3:-$SRC/$arch/proofs/$name.ml}
proof=$(cd "$(dirname "$proof")" && pwd)/$(basename "$proof")
tag=$(basename "$proof" .ml)

# Same theorem selection as proofs/hol_light/<arch>/list_thms.sh
{
  grep -hE "^[[:space:]]*let[[:space:]]+[^[:space:]]+[[:space:]]+=[[:space:]]+(time[[:space:]]+)?prove" "$proof" || true
} |
  sed -E "s/^[[:space:]]*let[[:space:]]+([^[:space:]]+)[[:space:]]+=.*/\1/" >"$OUT/$tag.thms"

wrapper="$OUT/$tag.trace.ml"
{
  echo "loadt \"$proof\";;"
  echo "holtrace_namethm ["
  while read -r t; do echo "  (\"$t\", $t);"; done <"$OUT/$tag.thms"
  echo "];;"
  echo "holtrace_stop ();;"
} >"$wrapper"

make -C "$ROOT/proofs/hol_light/$arch" "mlkem/$name.o"
if [[ $SRC != "$ROOT/proofs/hol_light" ]]; then
  cp "$ROOT/proofs/hol_light/$arch/mlkem/$name.o" "$SRC/$arch/mlkem/$name.o"
fi
"$ROOT/proofs/hol_light/$arch/proofs/build-proof.sh" "$wrapper" "$HOLDIR/hol.sh" "$OUT/$tag.trace.native"

cd "$SRC"
rm -f "$OUT/$tag.50"
HOLTRACE_SAVE="$OUT/$tag.50" /usr/bin/time -l "$OUT/$tag.trace.native" >"$OUT/$tag.trace.log" 2>&1 || {
  echo "trace run failed, see $OUT/$tag.trace.log"
  exit 1
}
rm -f "$OUT/$tag.trace.native"
ls -la "$OUT/$tag.50"
grep -E "Running time|real|maximum resident" "$OUT/$tag.trace.log" || true
