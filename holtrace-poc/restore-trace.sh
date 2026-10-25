#!/usr/bin/env bash
# Copyright (c) The mlkem-native project authors
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
#
# TEMPORARY PoC: replay a trace in a fresh HOL Light process that loads
# no s2n-bignum / mlkem-native code. See restore.ml.
#
# Usage (inside `nix develop .#hol_light`):
#   HOLTRACE_HOL=<HOL Light dir with holtrace.ml installed> \
#   holtrace-poc/restore-trace.sh <trace.50> <names file> [log file]

set -euo pipefail

trace=$(cd "$(dirname "$1")" && pwd)/$(basename "$1")
names=$(cd "$(dirname "$2")" && pwd)/$(basename "$2")
log=${3:-${trace%.50}.restore.log}
POC=$(cd "$(dirname "$0")" && pwd)
HOLDIR=${HOLTRACE_HOL:?set HOLTRACE_HOL}

bin=$(mktemp -d)/restore.native
"$POC/../proofs/hol_light/aarch64/proofs/build-proof.sh" "$POC/restore.ml" "$HOLDIR/hol.sh" "$bin" >/dev/null
# HOLTRACE_SAVE must be unset: we only replay, we do not record.
env -u HOLTRACE_SAVE HOLTRACE_RESTORE="$trace" HOLTRACE_NAMES="$names" \
  /usr/bin/time -l "$bin" >"$log" 2>&1 && rc=0 || rc=$?
rm -rf "$(dirname "$bin")"
grep -E "^(types|terms|theorems|inferences|axioms|typedefs|constants|named thms):|RESTORE|real|maximum resident|Failure|Assert|exception" "$log" || true
exit $rc
