#!/usr/bin/env bash
# Copyright (c) The mlkem-native project authors
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
#
# This tiny script lists HOL-Light theorem names declared as proofs.

ROOT=$(git rev-parse --show-toplevel)
cd "$ROOT" || exit

if [[ $# == 0 ]]; then
  set -- proofs/hol_light/x86_64/proofs/*.ml
fi

grep -hE "^[[:space:]]*let[[:space:]]+[^[:space:]]+[[:space:]]+=[[:space:]]+(time[[:space:]]+)?prove" "$@" |
  sed -E "s/^[[:space:]]*let[[:space:]]+([^[:space:]]+)[[:space:]]+=.*/\1/"
