[//]: # (SPDX-License-Identifier: CC-BY-4.0)

# Accepted definitions and statements

The files in this directory contain trusted or manually reviewed
definitions and theorems. Definitions are recorded in `*.defs` files,
theorems are recorded in `*.thms` files.

The directory has three layers:

- **Base layer** (`base/`): Definitions from the core infrastructure of
  HOL-Light and s2n-bignum. Those are the base definitions that we expect
  all our proofs to build on and reproduce upon replay. They must either
  be reviewed or trusted.
- **Spec** (`spec/`): Definitions of specifications used by our proofs.
  As with HOL-Light and s2n-bignum definitions, proof scripts are checked
  to not use conflicting definitions for these specifications. These must
  be reviewed by hand.
- **Proof** (`proofs/ARCH/`): The top-level statement of our correctness
  and security theorems, plus all required definitions not covered by the
  base and spec layers. These must be reviewed by hand.

Each file in `base/` and `spec/` records the pins or the source it was
generated from, and compare fails when they no longer match. A proof's
`FUNC.defs` includes its machine code as a byte list;
[check-binary](../../../../scripts/check-binary) compares that with
functions in binaries, through `proofs/hol_light/bind.yml`.

All files in this directory are auto-generated. To regenerate the files,
run `scripts/autogen --hol-trace-defs` in
`nix develop .#hol_light-cross`, or in `nix develop .#hol_light` for the
host's architecture only. `--hol-trace-defs base,specs,FUNC,...`
regenerates only those, and `--dry-run` fails if any is stale.

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

Renderings over 64 KiB are stored as their SHA-256 hash; CI checks those
in `base/` by regenerating it, and `--accept` adds one to a proof's
files only with `--accept-hashed`. A byte list is preceded by a comment
with its length and SHA-256, which check-binary checks. An axiom's
header is a hash of its text; `base/hol_light.defs` gives HOL Light's
names for its three axioms in comments.
