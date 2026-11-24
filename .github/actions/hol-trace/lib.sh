# Copyright (c) The mlkem-native project authors
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
# shellcheck shell=bash

# Shared by the steps of the HOLTrace action. HOLTRACE_PROOFS holds the
# selected proofs as ARCH/FUNC, separated by spaces.

set -o pipefail
ulimit -s 1048576

read -r -a proofs <<<"${HOLTRACE_PROOFS:-}"
for proof in "${proofs[@]}"; do
  if ! [[ $proof =~ ^(aarch64|x86_64)/[a-zA-Z0-9_]+$ ]]; then
    echo "invalid proof name: $proof" >&2
    exit 1
  fi
done

# Workers for each phase. hol-trace keeps one pool for the proofs of
# both architectures: a worker that finishes takes the next proof.
HOLTRACE_JOBS=${HOLTRACE_JOBS:-12}
