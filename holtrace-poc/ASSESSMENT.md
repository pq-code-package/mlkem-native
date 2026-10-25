[//]: # (SPDX-License-Identifier: CC-BY-4.0)

# HOLTrace for mlkem-native: assessment (temporary PoC)

Scope: can HOLTrace (<https://holtrace.cr.yp.to/>, release 20250714) add
confidence to the soundness story of our HOL Light proofs (SOUNDNESS.md,
Gap C1 and neighbours)? Everything here was run on an Apple M-series
laptop (18 cores, 48 GB, macOS), using the HOL Light (0-unstable-2026-05-19,
OCaml 5.4.1, module build) and s2n-bignum (bf75b6c) from our nix shell.

## Summary

HOLTrace is useful to us. Its value is not "a faster or smaller kernel".
It moves the proof check out of the process that ran the proof.

- **Recording.** `holtrace.ml` wraps the 10 primitive rules and the 3
  definition/axiom primitives of the HOL Light kernel. While our normal
  proof binary runs, every new kernel step is appended to a text trace.
- **Replay.** A *separate* HOL Light process that loads only core HOL
  Light plus `holtrace.ml`, and none of s2n-bignum's or our OCaml code,
  rebuilds every theorem from the trace through its own kernel. It
  checks that each rebuilt theorem equals the recorded statement.

What this removes from the trusted base of a proved theorem:

1. All non-kernel OCaml in the proof process: s2n-bignum (`common/`,
   `arm/`, `x86/`), our proof scripts, and the HOL Light derived rules
   they call. (The replay process still loads core HOL Light, but builds
   the replayed theorems only through kernel primitives.) If any of the
   proof-process code breaks the `thm` abstraction (by `Obj.magic`, `Marshal`, a C
   stub, a memory-safety bug, an OCaml miscompilation of 100k+ lines of
   proof code), the replay fails.
2. The CI harness's verdict. Today `proofs/hol_light/*/Makefile` decides
   "OK" by grepping the proof log for `error:`/`exception:` and
   `Running time:`. The proof script runs before `check_axioms ()` in the
   same OCaml scope and can rebind it. Replay replaces that verdict with
   "theorem NAME with statement S was rebuilt using only the 3 standard
   axioms".
3. The parsing/printing context for *reading* a statement. Interface
   overloads etc. live in the proof process. The replay prints the
   statement with real constant names.

What it does **not** remove:

- Bugs in the HOL Light kernel logic itself: replay uses the same
  `fusion.ml`. Bugs in OCaml that also hit the (much simpler) replay
  process.
- Gap A and Gap B (specification and model fidelity). HOLTrace does
  help to *audit* them: the trace holds the exact definitions and
  statements the kernel saw.

HOLTrace's two standalone checkers (`holtrace-verify-simple` in Python,
`holtrace-verify` in C) would also take HOL Light and OCaml out of the
loop. The author marks both as experimental and "likely to have soundness
bugs". They are a useful second opinion, not a replacement. I could not
build the C checker here (see README.md, "Not done").

**Cost is the catch.** Recording runs inside our native-compiled proof
binaries. With HOLTrace's `hashtt` mode plus a fix for an equality
performance bug, it was 8x slower and used 20x more memory on the
smallest proof: 633 s and 5.9 GB for `poly_reduce`, against 78 s and
294 MB. Without hashtt it was about 100x slower. This rules it out as a
per-PR check. It is reasonable as a nightly or pre-release job on a
large Linux machine, with the patches listed below. Replay cost on a real
mlkem trace is not measured yet.

## PoC results

PoC code: `holtrace-poc/` (temporary, branch `holtrace`). How to rerun: README.md.

### Attacks: current CI check vs. HOLTrace replay

Each attack is a proof script (`holtrace-poc/attacks/*.ml`) built with
`build-proof.sh`. It is judged by the Makefile's grep check, then recorded
under HOLTrace and replayed by `restore.ml`. The replay accepts new
definitions, rejects new axioms and checks every statement.

| Attack | What the proof log shows | CI check | HOLTrace replay |
|---|---|---|---|
| `hidden_axiom`: `new_axiom` + rebind `check_axioms` to a no-op | `\|- 1 = 2` | OK | REJECTED: `refusing new axiom` |
| `forge_objmagic`: `Obj.magic` builds `\|- F` | `\|- 1 = 2` | OK | REJECTED: statement check fails (`holtrace.ml` line 843) |
| `interface_spoof`: `overload_interface("+", fake_add)` | `\|- 2 + 2 = 5` | OK | ACCEPTED, prints `\|- fake_add 2 2 = 5` |

The third row is the expected behaviour. The theorem is true, and the
kernel was never fooled. But the replay shows what was really proved,
and `trace_tool.py closure` lists `fake_add` among the 18 definitions the
statement depends on. `forge_objmagic` was recorded with the `hashtt`
build and replayed with both builds (same verdict); the other two were
recorded and replayed with the plain build.

Note on threat model: s2n-bignum's SOUNDNESS.md assumes proof engineers
are not adversarial. The attacks stand in for accidents of the same
shape: unsafe OCaml in a library, a runtime/compiler bug, an accidental
rebinding of a checker, an overload that changes the meaning of a spec.
Today neither s2n-bignum nor our proofs use `Obj`/`Marshal` (checked with
grep); HOLTrace would keep it that way without review effort.

### Costs measured

| Run | Wall time | Peak RSS | Trace |
|---|---|---|---|
| Core HOL Light load, untraced | 8 s | 59 MB | - |
| Core HOL Light load, traced (`./install`) | 845 s | 1.3 GB | 82 MB |
| Core HOL Light load, traced (`./install+hashtt`) | 150 s (91 user, 54 sys) | 1.5 GB | 82 MB |
| Replay of an attack trace (core + tiny proof, plain build) | 40-49 s | 1.1 GB | - |
| `poly_reduce` (AArch64) proof, untraced | 78 s | 294 MB | - |
| `poly_reduce`, traced, plain | killed after 60 min CPU, ~85% through | 1.8 GB | >138 MB |
| `poly_reduce`, traced, hashtt, unpatched | stalled >20 min in `caml_equal` (killed) | 6.7 GB | 354 MB so far |
| `poly_reduce`, traced, hashtt + equality patch | 633 s (297 user, 319 sys) | 5.9 GB | 480 MB |
| Replay of the `poly_reduce` trace | not run yet | | |

HOLTrace's own documentation reports 14x (plain) and 3.4x (hashtt) for
the bytecode toplevel, where loading the core library takes 154 s
untraced (8 s native here). Against a fast native base, the tracing work
weighs far more. Three causes are visible in the code:

- Without hashtt, `Hashtbl` uses OCaml's generic hash, which looks at only
  10 meaningful words. The large, similar terms of symbolic simulation
  collide, and structural equality runs along long bucket chains.
- `trace` calls `Out_channel.flush` after every line, so there is one
  `write` system call per trace line (54 s of system time for the core).
- hashtt's hash-table `equal` functions use OCaml's structural `=`.
  `=` must report `nan <> nan`, so it does not stop at physically equal
  subvalues, and it walks heavily shared terms as trees. `sample` showed
  the stalled run spending all its time in `caml_equal`. Using
  `compare ... = 0` gives the same answer for HOL objects and does stop
  at shared subterms (`patch-holtrace-equality.sh`; also applied to the
  replay's statement checks).

Tracing also keeps every theorem, term and type alive in hash tables, so
memory grows with the whole session: 5.9 GB for poly_reduce, against
294 MB untraced. Under memory pressure (other apps on this laptop) the
hashtt run paged heavily; part of its 319 s system time is paging.

## Compatibility problems found (with workarounds in the PoC)

1. `install-worker` (`./install+hashtt`) crashes on macOS. It uses
   `multiprocessing.Pool` with no `if __name__ == '__main__'` guard, and
   macOS starts workers with `spawn`. The workaround is to run it with the
   `fork` start method.
2. hashtt adds a hash field to every constructor (`Comb of term * term *
   int`). Its source rewriter only patches files in the HOL Light
   directory. s2n-bignum and our proofs pattern-match on constructors
   about 4,200 times, so they need the same rewrite (49 files changed):
   `hashtt-prepare.sh`.
3. hashtt's rewriter counts commas without skipping string literals, so
   it leaves `Const(",",_)` and `Const(",,",_)` with two arguments. This
   breaks the build in HOL Light's `Library/words.ml` and s2n-bignum's
   `relational.ml`, `wordlist.ml`, `x86/proofs/{decode,x86}.ml`, ... The
   PoC patches these with a regex.
4. `holtrace_restore_allownew` accepts new *axioms*, not just new
   definitions. We need new definitions (s2n-bignum and our proofs define
   thousands of constants), so the replay must call
   `holtrace_restore_worker` with `allownewaxioms=false` (`restore.ml`).
5. `holtrace-verify-simple` accepts any `X` (axiom) line without
   reporting it. A user must check the axioms separately
   (`trace_tool.py axioms`).
6. In native mode there is no `update_database()`, so theorems must be
   named explicitly with `holtrace_namethm`. The PoC generates the list
   with the same regex as `list_thms.sh`.
7. hashtt's `equal` functions use structural `=` (see Costs). On
   poly_reduce this stalls recording; patched in the PoC.
8. `holtrace-verify.c` does not compile on macOS (`reallocarray`), and
   `pt2holtrace` needs Boost. Neither matters on Linux.

## Recommendation

1. Add an opt-in (nightly or pre-release) CI job on Linux: record all
   proofs with `install+hashtt` (plus the rewrites above), replay each
   trace with a plain `./install` HOL Light, and require:
   - no new axioms,
   - every name from `list_thms.sh` restored,
   - each statement equal to the recorded one.
   Keep the recording and replay builds separate: hashtt changes
   `fusion.ml`, but only the recording side runs it.
2. Run `holtrace-verify` and `holtrace-verify-simple` on the same traces
   as a second opinion. Check axioms separately. Treat disagreement as a
   finding, never acceptance as proof.
3. Use the trace as an audit artifact:
   - `trace_tool.py closure NAME` lists exactly the definitions a
     theorem's meaning rests on. This is useful for Gap A3 reviews.
   - `trace_tool.py bytes <fn>_mc` extracts the verified machine code
     from the trace, independently of HOL Light's ELF loader. That is a
     starting point for #1602 (checking reassembled code against the
     proved bytes).
4. Clarify C1 in our SOUNDNESS.md (and suggest the same upstream). The
   s2n-bignum text says traces are
   "independently verifiable by a standalone checker, completely
   bypassing both the HOL Light code and the OCaml runtime". That is
   true only for the experimental checkers. The recommended
   `holtrace_restore` runs HOL Light on OCaml, and it removes the
   *non-kernel* code from the TCB, not the kernel.
5. Longer term: replaying traces in Candle (verified HOL Light clone on
   CakeML) would take OCaml and the unverified kernel out of the loop.
   That needs a port of the restore loop to Candle; I have not tried it.

Upstream patches worth sending to HOLTrace: points 1, 3 and 7 above, an
option to flush less often, and a restore variant that accepts new
definitions but not new axioms.

## Licensing

No concern. HOLTrace is public domain, also offered as `LicenseRef-PD-hp
OR CC0-1.0 OR 0BSD OR MIT-0 OR MIT`. All are permissive and compatible
with `Apache-2.0 OR ISC OR MIT`. The PoC downloads HOLTrace rather than
vendoring it. See README.md for details, including what to do if we
vendor it later.
