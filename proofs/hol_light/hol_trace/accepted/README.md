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
  |- (= MLKEM_Q #3329)
```

Objects are printed as fully parenthesized prefix expressions:

| Text | Meaning |
|---|---|
| `(f a b)` | `f` applied to `a`, then `b` |
| `(\x:ty. body)` | abstraction over the variable `x` of type `ty` |
| `x` | the variable bound by the innermost binder named `x` |
| `{x:ty}` | any other variable `x` of type `ty`, for example a free one |
| `c`, `c:ty` | a constant; its type is shown unless its generic type and its arguments determine it |
| `$c`, `$c:ty` | a constant whose name is bound by an enclosing binder |
| `#12` | the numeral `NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 _0))))` |
| `&12` | the integer `int_of_num #12` |
| `[a; b]` | `CONS a (CONS b NIL)` |
| `#x[0a ff]` | the byte list `[word 10; word 255]`, when every element is `word n` with a canonical numeral `n` < 256 |
| `'A`, `(a -> b)`, `(list num)` | a type variable, a function type, a type constructor |
| `(a # b # c)` | the product type `prod a (prod b c)` |
| `#64` | the numeral type `tybit0 (... 1)` |
| `_1`, `'?1` | generated variables and parser-invented type variables, renumbered in order of first occurrence |
| `"GEN%PVAR%1"` | a variable that the parser invents for a set comprehension, renumbered likewise |
| `_<C>` | the temporary constant that `define_type` creates for the constructor `C`, defined by `C = _<C>`; HOL Light calls it `_<n>` |

Names are printed as written if they are alphanumeric, or symbolic and
not the name of a variable or type variable, and as JSON strings
otherwise: a variable named `+` is `"+"` wherever it appears.
Type-definition entries always show the types of their abs and rep
constants, which give the order of the new type's arguments. Different
objects never print the same, except for the renumbering, which is a
bijection that keeps the structure of the term; HOL Light numbers these
names by global counters, so they depend on load order and on how many
fresh names earlier proofs used. A temporary constant is shown as
`_<C>` only if exactly one definition has the form `C = _<n>`;
otherwise it keeps its name `_<n>`.

Renderings longer than 64 KiB are stored as their SHA-256 hash. Today
only s2n-bignum's instruction decoders and execution functions, its x86
`instruction` type and its arm `__opaque_bitmatch_3` are that large;
they are trusted through the s2n-bignum pin. `--accept` refuses
to add or change a hashed entry in a proof's file unless
`--accept-hashed` is given, and never stores a main theorem as a hash.

A definition whose rendering is a byte list, `|- (= c #x[...])`, is
preceded by a comment with its length and SHA-256, for example

```
# poly_tomont_asm_mc: 204 bytes, sha256 064c8bdd...
```

The comment is written by `--accept`; check-binary recomputes it from the
hex and fails if they disagree.
