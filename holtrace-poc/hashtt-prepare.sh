#!/usr/bin/env bash
# Copyright (c) The mlkem-native project authors
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
#
# TEMPORARY PoC: prepare sources for tracing with HOLTrace's `hashtt` mode.
#
# hashtt adds a cached hash field to every HOL type, term and theorem
# constructor in fusion.ml (e.g. `Comb of term * term * int`). OCaml code
# outside HOL Light that pattern-matches on `Comb(f,x)` etc. must be
# rewritten to `Comb(f,x,_)`. HOLTrace's installer does this only for the
# HOL Light directory; this script applies the same rewrite (the `process`
# function from HOLTrace's install-worker) to copies of s2n-bignum and of
# proofs/hol_light (including the already assembled object files).
#
# Usage (inside `nix develop .#hol_light`, after the objects are built):
#   HOLTRACE_SRC=<holtrace-YYYYMMDD dir> DEST=<dir> holtrace-poc/hashtt-prepare.sh
#
# Creates $DEST/s2n_bignum, $DEST/mlkem_native and $DEST/imports/ with the
# symlinks that IMPORTS_DIR expects.

set -euo pipefail

POC=$(cd "$(dirname "$0")" && pwd)
ROOT=$(git -C "$POC" rev-parse --show-toplevel)
HT=${HOLTRACE_SRC:?set HOLTRACE_SRC}
DEST=${DEST:?set DEST}

rm -rf "$DEST"
mkdir -p "$DEST/imports"
cp -a "$S2N_BIGNUM_DIR" "$DEST/s2n_bignum"
chmod -R u+w "$DEST/s2n_bignum"
cp -a "$ROOT/proofs/hol_light" "$DEST/mlkem_native"
rm -rf "$DEST/mlkem_native/.imports"
ln -s "$DEST/s2n_bignum" "$DEST/imports/s2n_bignum"
ln -s "$DEST/mlkem_native" "$DEST/imports/mlkem_native"

# The installer's rewriter counts commas without skipping string literals,
# so it leaves e.g. `Const(",",_)` and `Const(",,",_)` with two arguments.
# Patch those afterwards, here and in the hashtt HOL Light directory
# ($HOLTRACE_HOL, which provides Library/words.ml etc.).
python3 - "$HT/install-worker" "$DEST/s2n_bignum" "$DEST/mlkem_native" <<'EOF'
import os, re, sys
src = open(sys.argv[1]).read()
# Take only the function definitions; the installer's main part follows.
ns = {}
exec(compile(src[:src.index('# ===== main')], 'install-worker', 'exec'), ns)
changed = 0
for d in sys.argv[2:]:
    for sub, _, files in os.walk(d):
        for fn in files:
            if fn.endswith('.ml'):
                p = os.path.join(sub, fn)
                x = open(p).read()
                y = ns['process'](x)
                if y != x:
                    open(p, 'w').write(y)
                    changed += 1
print(f'hashtt rewrite: {changed} files changed')
EOF

python3 - "$DEST/s2n_bignum" "$DEST/mlkem_native" ${HOLTRACE_HOL:+"$HOLTRACE_HOL"} <<'EOF'
import os, re, sys
pat = re.compile(r'\b(Const|Var|Tyapp)\(("[^"]*"),([^,()]*)\)')
for d in sys.argv[1:]:
    for sub, _, files in os.walk(d):
        for fn in files:
            if fn.endswith('.ml'):
                p = os.path.join(sub, fn)
                x = open(p, encoding='latin-1').read()
                y = pat.sub(r'\1(\2,\3,_)', x)
                if y != x:
                    open(p, 'w', encoding='latin-1').write(y)
                    print(f'comma-literal fix: {p}')
EOF
