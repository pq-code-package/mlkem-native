[//]: # (SPDX-License-Identifier: CC-BY-4.0)

# hol-trace: re-checking the HOL Light proofs by replay

This directory builds on the idea and implementation of
[HOLTrace](https://holtrace.cr.yp.to/) to reduce the trusted computing
base (TCB) for the verification of mlkem-native's HOL Light proofs.

## Problem

Our HOL Light proof scripts are ordinary OCaml scripts. They succeed if
they run successfully in OCaml. It is the _intent_ that proof scripts
are descriptions of interactions with the HOL Light kernel through its
specified interface, but this is not enforced: for example, unsafe OCaml
can circumvent the kernel boundary and construct invalid theorems.

Further, the kernel allows the addition of new axioms that can
invalidate the apparent meaning of theorems. The same holds if proof
scripts don't load standard libraries (e.g. the HOL Light prelude or the
s2n-bignum base theories) but instead provide alternative and
inequivalent definitions of constants that the user then wrongly assumes
to carry their standard meaning.

Especially with very complex, AI-generated proofs, it can be difficult to
see whether a proof script is genuine or whether it is cheating in any of
the above ways.

## Solution

The idea behind [HOLTrace](https://holtrace.cr.yp.to/) is to capture the
kernel interactions emitted by a proof script, and use a trusted checker
to replay them against the -- or in fact _any_ -- implementation of the
HOL Light kernel.

The trace checker confirms that the trace uses no axioms beyond HOL
Light's own, and that the theorems it proves are the expected
statements. A proof script is thereby reduced to the kernel trace it
emits, and any other potential kernel bypass is irrelevant at the trace
level.

Deviating from HOLTrace slightly, we also extract the constant and type
definitions that a theorem relies on, and compare them against pinned
recordings of trusted definitions. For example, most traces will begin
by loading the HOL Light and s2n-bignum prelude, emitting a series of
type and constant definitions, including the architecture models. Those
definitions need to be generated in a trusted manner for every pin of
HOL Light and s2n-bignum, and are compared against when replaying
traces. If a definition that a theorem relies on has the name of a
definition from the prelude but differs from it, the check fails. This
catches cheating attempts where no new axioms are introduced, but the
underlying definitions are simply not what comes from HOL Light and
s2n-bignum.

Those type and constant definitions that a proof trace relies on but
that are not part of the prelude or other pre-validated lists of
definitions are emitted to a proof-specific file and need to be
validated by eye. The proof's machine code is listed there too, as a
byte list in hex with its SHA-256. A separate script,
[check-bind](check-bind), compares those byte lists to the backend
object files.

## How it works

1. **Record** (`hol-trace gen`): runs selected proofs under HOLTrace's
   recording build, which appends every type, term, theorem, inference
   and definition to a trace (`traces/ARCH/FUNC.50`), then prunes the trace
   to what the main theorems (`ARCH/list_thms.sh`) need. Note that this is
   a very memory-intensive process that takes hours and consumes
   >100G of RAM and disk space.
2. **Replay** (`hol-trace replay`): rebuild the trace in a separate HOL
   Light process that loads no proof code ([restore.ml](restore.ml)), and
   write the resulting theory to a result file; the result format is
   described in [term_encoding.ml](term_encoding.ml).
3. **Conform** (`hol-trace conform`): check the result against
   [accepted/](accepted) as described above; [conform.py](conform.py)
   lists the exact rules, and [accepted/README.md](accepted/README.md)
   the layout, the notation, and how each part is generated.
4. **Bind** (`check-bind`): compare the byte lists named in
   `accepted/proofs/ARCH/FUNC.bind` with sections of object files. This
   step needs no trace; it reads the object files as they are, so build
   them first, e.g. `make -B -C proofs/hol_light/ARCH mlkem/FUNC.o`.
   To reproduce a section's hash by hand:
   `readelf -x .text FUNC.o | grep '^  0x' | cut -c14-48 | xxd -r -p | sha256sum`.

`hol-trace check` is replay followed by conform.

## What is trusted

- **Trusted:**
  - the selected replay backend's kernel and result writer, and their
    language implementation. The rest of a backend, which decodes the
    trace, can make a check fail but not pass, since it builds theorems
    only through the kernel and conform compares every statement;
  - `hol-trace`, which picks the theorems and layers for each check;
  - [conform.py](conform.py) and [term_encoding.ml](term_encoding.ml);
  - the accepted files and the `.bind` files;
  - `check-bind`, and the assembler and Makefile that build the object
    files it reads;
  - `build-proof.sh`, which compiles `restore.ml` and the layer dumps;
  - `list_proofs.sh` and `list_thms.sh`;
  - Python, and the nix pins and shell that provide all of these;
  - for `hol-trace layers` only: the pinned HOL Light, s2n-bignum and
    the specification files, which run in the process that writes
    `accepted/base` and `accepted/spec`.
- **Not trusted:** everything that produces the trace in `gen`: the
  proof scripts, HOL Light and s2n-bignum as they load, the recording
  build and its patches ([nix/hol_trace](../../../nix/hol_trace); only
  0001 touches replay code), `holtrace-prune`, and trace storage. A
  fault there can make the check fail, but not pass.

## Usage

```bash
nix develop .#hol_trace-cross
hol-trace list
hol-trace layers                # same as scripts/autogen --hol-trace-defs
hol-trace gen [-p ARCH/FUNC ...] [--no-prune] [-j N]
hol-trace check [--backend BACKEND] [-p ARCH/FUNC ...] [-j N] [--accept]
hol-trace selfcheck
check-bind [accepted/proofs/ARCH/FUNC.bind ...]
```

`check` is `replay` followed by `conform`; both are also available
separately, and `conform` can be rerun without replaying. Without `-p`,
the commands select every function of both architectures (see
`hol-trace list`). `hol-trace --help` lists all options. Every command
first runs `selfcheck`, the unit tests of conform.py and check-bind
(under a second).
