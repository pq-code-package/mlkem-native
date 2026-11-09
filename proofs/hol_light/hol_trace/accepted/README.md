[//]: # (SPDX-License-Identifier: CC-BY-4.0)

# Accepted definitions and statements

`hol-trace compare` accepts a replayed proof only if every axiom appears
in `base/hol_light.defs`, and every definition that its main theorems
use and every main theorem appears here exactly. No other file may list
an axiom; `hol-trace outline` fails if a later load step adds one. A
proof's `FUNC.defs` includes its machine code as a byte list;
[check-binary](../../../../scripts/check-binary) compares that with functions in binaries,
through `proofs/hol_light/bind.yml`. See [../README.md](../README.md)
for the checks; the notation is below.

| Directory | Contents | Written by | Review |
|---|---|---|---|
| `base/` | HOL Light's axioms and definitions, and the s2n-bignum files that the proofs load (one file per architecture) | `hol-trace outline --base` | check that a diff is explained by a pin change |
| `spec/` | each mlkem-native file that the proofs load and that is not a proof: `spec/NAME.defs` for `common/NAME.ml`, `spec/ARCH/NAME.defs` for `ARCH/proofs/NAME.ml` | `hol-trace outline --specs` | careful: these are the specifications |
| `proofs/ARCH/` | per proof: `FUNC.thms`, the main theorems, and `FUNC.defs`, the definitions it uses beyond the layers | `hol-trace outline` or `hol-trace compare --accept` | careful: this is what the proof claims |

`base/` and `spec/` hold everything that each load step defines, whether
or not a proof uses it. Each file records the pins or the source file it
was generated from; conform fails when they no longer match.

`proofs/ARCH/FUNC.*` hold only what that proof needs beyond the layers,
usually a few constants and the statements.

To regenerate the files, run in
`nix develop .#hol_light-cross`; in `nix develop .#hol_light`, autogen
writes the proofs' files of the host's architecture only:

```bash
scripts/autogen --hol-trace-defs
```

`hol-trace outline` loads files with `prove` replaced by one that
asserts its goal, so it makes every definition but proves no theorem.
It first loads the pinned HOL Light, then the s2n-bignum files, then
each specification file, in one process for each architecture, and
writes the definitions that each step adds to `base/` and `spec/`. It
then loads each proof of one architecture, the host's or `--arch`'s, in
a process of its own and rewrites the proof's files as `hol-trace
compare --accept` does. `hol-trace outline --base` writes only `base/`,
`--specs` only `spec/`, and `-p FUNC ...` only those proofs' files.
`scripts/autogen --hol-trace-defs` runs `--base --specs` and then
writes the outlines of every proof of both architectures. With
`-j 12`, writing all outlines took 17 minutes, each proof 37 to 217 s
and at most 0.4 GiB; `gen` takes up to hours and over 100 GB per proof.

An outline checks nothing: it asserts every statement, true or not. The
files it writes are for review, and `hol-trace check`
confirms them against a replayed trace. If a definition did depend on a
proof, for example on whether it succeeds, an outline could have a
different entry; that replay would then fail, not pass.
`hol-trace compare --accept` rewrites a proof's files from a replay
result and never changes `base/` or `spec/`.

## Entries and notation

An entry is a header line, the object indented by two spaces, and a
blank line:

```
definition MLKEM_Q
  |- MLKEM_Q = 3329
```

Objects are printed as HOL Light prints them: its binders, `let`, infix
operators with their precedences, numerals (`&12` is `int_of_num 12`),
lists, and s2n-bignum's word types (`int64` is `64 word`). Line breaks
carry no meaning. Where HOL Light's printing is ambiguous, the notation
differs, so that different objects never print the same:

| Text | Meaning |
|---|---|
| `{x:ty}` | a variable that is free, or whose binder is hidden by an inner binder of the same name and another type |
| `(c args : ty)` | the application of `c` to `args` has type `ty`; shown where the type does not follow from `c` and `args` |
| `(op)` | an operator or keyword used as a constant without its notation, e.g. `(/\)` |
| `$c` | a constant whose name is bound by an enclosing binder |
| `"+"`, `"abs"` | a name that is a keyword, or neither alphanumeric nor symbolic |
| `-x` | `int_neg x` |
| `specification "c" f:ty. body` | `(@f. !g. body[f g]) (99, ...)`, the form in which `define` defines `c`; the tuple holds the character codes of `c` |
| `#x[0a ff]` | the byte list `[word 10; word 255]` |
| `_1`, `'?1`, `"GEN%PVAR%1"` | generated names, renumbered in order of first occurrence because HOL Light's counters depend on load order |
| `_<C>` | the temporary constant that `define_type` creates for the constructor `C` |

Renderings over 64 KiB are stored as their SHA-256 hash, and `--accept`
adds one to a proof's files only with `--accept-hashed`. A byte list is preceded by a comment
with its length and SHA-256, which check-binary checks. An axiom's
header is a hash of its text.
