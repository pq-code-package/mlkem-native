[//]: # (SPDX-License-Identifier: CC-BY-4.0)

# HOLTrace PoC: handover

Temporary proof-of-concept for using HOLTrace (<https://holtrace.cr.yp.to/>)
to re-check our HOL Light proofs. Findings and recommendation:
[ASSESSMENT.md](ASSESSMENT.md). This file covers how to continue the work
on another machine.

## State at handover (2026-10-25)

Done (on an M-series Mac, macOS, 48 GB):

- HOLTrace 20250714 installed into two copies of the nix HOL Light
  (0-unstable-2026-05-19): plain (`./install`) and `./install+hashtt`.
  Several HOLTrace issues found and worked around (ASSESSMENT.md,
  "Compatibility problems").
- Three attack proofs, each run through the current CI check and through
  HOLTrace record + replay, all with the expected verdicts. `forge_objmagic`
  was replayed with both builds; the other two with the plain build only.
- Cost of tracing the core HOL Light library: 845 s plain, 150 s hashtt,
  vs 8 s untraced.
- Traced AArch64 `mlkem_poly_reduce_aarch64_asm` with hashtt and the
  equality patch: 633 s wall (297 user, 319 sys), 5.9 GB peak RSS,
  480 MB trace. Untraced: 78 s, 294 MB. Without the equality patch it
  stalled; without hashtt it ran for over 60 min (killed). The laptop was
  under memory pressure from other programs, so the system time is
  inflated by paging.

Not done:

1. **Replay of the poly_reduce trace** (restore-trace.sh): never run.
   This is the key missing result: does a real s2n-bignum-based proof
   replay in a clean process, and at what cost?
2. **`trace_tool.py closure` / `bytes` on a real mlkem trace.** `closure`,
   `show` and `axioms` were tested on the attack traces only; `bytes` is
   untested.
3. **HOLTrace's standalone checkers** (`holtrace-verify`,
   `holtrace-verify-simple`): not run. Locally, the permission classifier
   refused compiling the downloaded C code, and `holtrace-verify.c` also
   needs a `reallocarray` shim on macOS. On Linux, `make -j8` in the
   HOLTrace directory should build them.
4. Any x86_64 proof; any proof larger than poly_reduce; all proofs.
5. Upstream reports to HOLTrace (see ASSESSMENT.md).

## Files

| File | Purpose |
|---|---|
| `ASSESSMENT.md` | Findings, measurements, recommendation |
| `setup.sh` | Download HOLTrace (sha256-checked), build both HOL Light copies |
| `patch-holtrace-equality.sh` | Replace structural `=` by `compare ... = 0` in `holtrace.ml` (applied by setup.sh) |
| `hashtt-prepare.sh` | Rewrite copies of s2n-bignum and `proofs/hol_light` for hashtt's changed constructors; fix the comma-literal bug in HOL Light `Library/` too |
| `trace-proof.sh` | Build and run one proof with `HOLTRACE_SAVE` set, naming the theorems found by the `list_thms.sh` regex |
| `restore.ml`, `restore-trace.sh` | Replay a trace in a process without s2n-bignum / mlkem-native code. Policy: new definitions allowed, new axioms refused, every statement checked |
| `baseline-proof.sh` | Same proof with stock HOL Light, for timing |
| `run-attacks.sh`, `attacks/*.ml` | CI check vs. record + replay for three attack scripts |
| `trace_tool.py` | Read a trace without HOL Light: `summary`, `axioms`, `show NAME`, `closure NAME`, `bytes CONST` |

## Reproducing on a Linux machine

Prerequisites: nix with flakes, this branch checked out, ideally 64 GB of
RAM or more. Tracing keeps every theorem in memory. On an x86_64 host,
use `nix develop .#hol_light-cross-aarch64` for AArch64 proofs. On an
aarch64 host, use `nix develop .#hol_light-cross-x86_64` for x86_64
proofs. All commands below run from the repository root inside that
shell.

```bash
export WORK=$HOME/holtrace-work           # anything outside the repo

# 1. HOLTrace + two HOL Light builds (about 3 minutes)
holtrace-poc/setup.sh
HT=$WORK/dl/holtrace-20250714

# 2. hashtt-rewritten copies of s2n-bignum and proofs/hol_light
HOLTRACE_HOL=$WORK/hol-light-hashtt HOLTRACE_SRC=$HT DEST=$WORK/hashtt-src \
  holtrace-poc/hashtt-prepare.sh

# 3. Record one proof (hashtt build, rewritten sources)
D=$WORK/hashtt-src
HOLTRACE_HOL=$WORK/hol-light-hashtt PROOF_SRC=$D/mlkem_native \
  IMPORTS_DIR=$D/imports S2N_BIGNUM_DIR=$D/s2n_bignum OUT=$WORK/out \
  holtrace-poc/trace-proof.sh aarch64 mlkem_poly_reduce_aarch64_asm

# 4. Replay it with the plain build (the one we would trust)
HOLTRACE_HOL=$WORK/hol-light-trace holtrace-poc/restore-trace.sh \
  $WORK/out/mlkem_poly_reduce_aarch64_asm.50 \
  $WORK/out/mlkem_poly_reduce_aarch64_asm.thms
# Expect "RESTORE OK", "axioms: 3" and one RESTORED block per theorem.
# Full log: $WORK/out/mlkem_poly_reduce_aarch64_asm.restore.log

# 5. Audit questions, no HOL Light needed
T=$WORK/out/mlkem_poly_reduce_aarch64_asm.50
python3 -I holtrace-poc/trace_tool.py $T summary
python3 -I holtrace-poc/trace_tool.py $T axioms        # expect the 3 standard
python3 -I holtrace-poc/trace_tool.py $T closure MLKEM_POLY_REDUCE_SUBROUTINE_CORRECT
python3 -I holtrace-poc/trace_tool.py $T bytes mlkem_poly_reduce_mc
#   compare with the BYTECODE list in
#   proofs/hol_light/aarch64/proofs/mlkem_poly_reduce_aarch64_asm.ml

# 6. Attacks (plain build records and replays; about 15 min each)
HOLTRACE_HOL=$WORK/hol-light-trace OUT=$WORK/attacks holtrace-poc/run-attacks.sh

# 7. Untraced baseline for comparison
OUT=$WORK/out holtrace-poc/baseline-proof.sh aarch64 mlkem_poly_reduce_aarch64_asm

# 8. Standalone checkers (Linux; not yet tried anywhere)
make -C $HT -j8
$HT/holtrace-verify < $T
pypy3 $HT/holtrace-verify-simple < $T   # or python3; slow on big traces
```

Notes:

- `trace-proof.sh` records the *whole* process: core HOL Light, the
  s2n-bignum base, then the proof. The core alone is an 82 MB trace.
- `run-attacks.sh` records *and* replays with `HOLTRACE_HOL`. With the
  plain build, recording takes about 15 min per attack (core library).
  The hashtt build also works for the attacks, because they do not load
  s2n-bignum. To replay a hashtt-recorded trace with the plain build,
  call `restore-trace.sh` separately.
- `holtrace_restore` prints one `matching ...` or `creating ...` line
  per definition; the `RESTORE*` lines are the summary.
- Shrinking traces with `holtrace-prune` (Python) before replay or
  checking was not tried.

## Suggested next steps, in order

1. Steps 3-5 above for poly_reduce. Record replay time and memory, and
   the closure size (number of definitions behind the statement).
2. Step 8 on the same trace: do both standalone checkers accept it, and
   in what time?
3. Record and replay one large proof (e.g. `mlkem_ntt_aarch64_asm`) to
   see how cost scales.
4. Decide on the CI shape (ASSESSMENT.md, Recommendation), then turn the
   scripts into a proper `scripts/` tool and drop this directory.
5. Report the HOLTrace issues upstream (Bernstein; contact via the
   HOLTrace site).

## Licensing

HOLTrace is public domain (`doc/license.md` in the tarball). It is also
offered under the SPDX expression `LicenseRef-PD-hp OR CC0-1.0 OR 0BSD OR
MIT-0 OR MIT`. Each option is permissive and compatible with
mlkem-native's `Apache-2.0 OR ISC OR MIT`. There is no attribution or
copyleft obligation.

- This directory does not vendor HOLTrace. `setup.sh` downloads it.
  `hashtt-prepare.sh` runs the rewrite function from HOLTrace's
  `install-worker` at run time. `patch-holtrace-equality.sh` contains
  short search/replace snippets of `holtrace.ml`.
- If we ever vendor HOLTrace files, pick one of the SPDX options (e.g.
  `MIT-0` or `0BSD`; REUSE tooling would need a license text for the
  custom `LicenseRef-PD-hp`). Add SPDX headers ourselves, because the
  individual HOLTrace source files have none. Record the source and
  version as we do for other imports.
- `pt2holtrace.cc` needs Boost (Boost Software License) to build. We do
  not need that tool.
- The traces are data derived from HOL Light (2-clause-BSD-style
  licence; some files differ),
  s2n-bignum (`Apache-2.0 OR ISC OR MIT-0`) and our proofs. If we
  publish traces, for example as CI artifacts, the same permissive
  licences apply.
