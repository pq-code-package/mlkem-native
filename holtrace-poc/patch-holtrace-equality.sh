#!/usr/bin/env bash
# Copyright (c) The mlkem-native project authors
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
#
# TEMPORARY PoC: replace structural `=` on HOL objects in an installed
# holtrace.ml by `compare ... = 0`.
#
# OCaml's `=` (caml_equal) does not stop at physically equal subvalues,
# because it must report nan <> nan. HOL terms from symbolic simulation
# share subterms heavily, so `=` walks them as trees, which can take
# exponential time. `compare` does stop at physically equal subvalues
# and gives the same answer for HOL types, terms and theorems (they hold
# no floats or closures). With hashtt, the `equal` functions of the hash
# tables use `=`; a traced poly_reduce proof spent >20 min in caml_equal.
#
# Usage: holtrace-poc/patch-holtrace-equality.sh <HOL Light dir>
# Afterwards rebuild hol_lib (see README in this directory).

set -euo pipefail
f=$1/holtrace.ml
python3 - "$f" <<'EOF'
import sys
p = sys.argv[1]
s = open(p).read()
rules = [
    ("((hash_type ty0 = hash_type ty1) && (ty0 = ty1))",
     "((hash_type ty0 = hash_type ty1) && (compare ty0 ty1 = 0))"),
    ("((hash_term tm0 = hash_term tm1) && (tm0 = tm1))",
     "((hash_term tm0 = hash_term tm1) && (compare tm0 tm1 = 0))"),
    ("((hash_thm th0 = hash_thm th1) && equals_thm th0 th1)",
     "((hash_thm th0 = hash_thm th1) && (compare (dest_thm th0) (dest_thm th1) = 0))"),
    ("assert((hhh,c) = dest_thm(thm))",
     "assert(compare (hhh,c) (dest_thm thm) = 0)"),
    ("assert(dest_thm known = dest_thm th)",
     "assert(compare (dest_thm known) (dest_thm th) = 0)"),
    ("let istarget f = (dest_thm f = target) in",
     "let istarget f = (compare (dest_thm f) target = 0) in"),
]
n = 0
for old, new in rules:
    if old in s:
        s = s.replace(old, new)
        n += 1
open(p, 'w').write(s)
print(f'{p}: {n} replacements')
EOF
