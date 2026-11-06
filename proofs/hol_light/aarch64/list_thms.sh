#!/usr/bin/env bash
# Copyright (c) The mlkem-native project authors
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
#
# Lists the main theorems of the AArch64 HOL-Light proofs, one per line.
# These are the theorems each proof must establish (checked by `lint`)
# and the ones `hol-trace` records and checks. Only the subroutine
# theorems, which describe a call of the routine, are listed; the core
# theorems that they are derived from are intermediate results.
#
# The prefix is the routine name without _aarch64_asm, in upper case. It
# carries the namespace (`mlkem_` for arithmetic, none for the
# namespace-agnostic Keccak proofs). For routine foo_aarch64_asm:
#   FOO_SUBROUTINE_CORRECT, FOO_SUBROUTINE_SAFE
# rej_uniform has no constant-time proof and uses MEMSAFE instead of SAFE.
#
# Usage: list_thms.sh [ROUTINE...]  (default: all routines of list_proofs.sh)

set -euo pipefail

if [[ $# == 0 ]]; then
  routines=$("$(dirname "$(realpath "$0")")/list_proofs.sh")
  # shellcheck disable=SC2086 # routine names contain no spaces
  set -- $routines
fi

for routine in "$@"; do
  prefix=$(echo "${routine%_aarch64_asm}" | tr '[:lower:]' '[:upper:]')
  safe=SAFE
  [[ $routine == mlkem_rej_uniform_* ]] && safe=MEMSAFE
  echo "${prefix}_SUBROUTINE_CORRECT"
  echo "${prefix}_SUBROUTINE_${safe}"
done
