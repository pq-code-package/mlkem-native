#!/usr/bin/env bash
# Copyright (c) The mlkem-native project authors
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
#
# TEMPORARY PoC: download HOLTrace and build two HOL Light copies with it.
#
#   $WORK/hol-light-trace   holtrace.ml only (`./install`): use for replay
#   $WORK/hol-light-hashtt  holtrace.ml + hashtt (`./install+hashtt`): use
#                           for recording traces
#
# Both get patch-holtrace-equality.sh applied. Run inside
# `nix develop .#hol_light` (needs $HOLLIGHT_DIR, ocaml, camlp5, zarith).
#
# Usage: WORK=/path/to/workdir holtrace-poc/setup.sh

set -euo pipefail

POC=$(cd "$(dirname "$0")" && pwd)
WORK=${WORK:-/tmp/holtrace-poc}
VERSION=20250714
SHA256=3c5f8be726d3b3c9f06b93f7a58ce49d624f9e36dcfdf6e9e9cdb9fe64528972
HOL=${HOLLIGHT_DIR:?run inside nix develop .#hol_light}

for d in "$WORK/dl" "$WORK/hol-light-trace" "$WORK/hol-light-hashtt"; do
  if [[ -e $d ]]; then
    echo "$d exists; remove it or pick another WORK" >&2
    exit 1
  fi
done

# Download into its own directory and check the hash recorded in
# ASSESSMENT.md before unpacking.
mkdir -p "$WORK/dl"
curl -sSfL -o "$WORK/dl/holtrace-$VERSION.tar.gz" "https://holtrace.cr.yp.to/holtrace-$VERSION.tar.gz"
if command -v sha256sum >/dev/null; then
  got=$(sha256sum "$WORK/dl/holtrace-$VERSION.tar.gz" | cut -d' ' -f1)
else
  got=$(shasum -a 256 "$WORK/dl/holtrace-$VERSION.tar.gz" | cut -d' ' -f1)
fi
if [[ $got != "$SHA256" ]]; then
  echo "sha256 mismatch: $got" >&2
  exit 1
fi
tar -xzf "$WORK/dl/holtrace-$VERSION.tar.gz" -C "$WORK/dl"
HT=$WORK/dl/holtrace-$VERSION

# HOLTrace's installer edits hol_lib.ml (loads holtrace.ml before nets.ml)
# and, for hashtt, rewrites every .ml file in the HOL Light directory. It
# uses multiprocessing without a __main__ guard, which breaks with the
# `spawn` start method (macOS default), so force `fork`.
install_holtrace()
{
  (cd "$HT" && python3 -c "
import sys, multiprocessing
multiprocessing.set_start_method('fork')
sys.argv = ['install-worker', '$1', '$2']
exec(compile(open('install-worker').read(), 'install-worker', 'exec'))
")
}

for v in trace hashtt; do
  dir=$WORK/hol-light-$v
  cp -a "$HOL" "$dir"
  chmod -R u+w "$dir"
  if [[ $v == trace ]]; then
    install_holtrace install "$dir"
  else
    install_holtrace install+hashtt "$dir"
  fi
  "$POC/patch-holtrace-equality.sh" "$dir"
  touch "$dir/hol_lib.ml"
  make -C "$dir" HOLLIGHT_USE_MODULE=1 hol_lib_inlined.ml hol_lib.cmo hol_lib.cma hol_lib.cmxa
  # The copied hol.sh points at the nix store; point it at this copy.
  sed "s^__DIR__^$dir^g; s^__USE_MODULE__^1^g" "$dir/hol_4.14.sh" >"$dir/hol.sh"
  chmod +x "$dir/hol.sh"
done

# hashtt's rewriter misses constructor patterns whose string literal
# contains a comma; hashtt-prepare.sh fixes those (also in Library/).
echo
echo "Done. Next, for recording with hashtt:"
echo "  HOLTRACE_HOL=$WORK/hol-light-hashtt HOLTRACE_SRC=$HT DEST=$WORK/hashtt-src $POC/hashtt-prepare.sh"
