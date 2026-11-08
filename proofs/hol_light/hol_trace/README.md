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
Light's own, and that the theorems it proves are the expected statements
recorded in [accepted/](accepted). A proof script is thereby reduced to
the kernel trace it emits, and any other potential kernel bypass is
irrelevant at the trace level.

HOLTrace's recommended check, `holtrace_restore`, runs in a HOL Light
session that has the trusted libraries loaded, and refuses any
definition in the trace that the session does not already have. We
deviate from this: replay starts from core HOL Light only, without
s2n-bignum or the specification files, and lets the trace make its own
definitions. We then extract the constant and type definitions that a
theorem relies on, and compare them against pinned recordings of
trusted definitions. For example, most traces will begin
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
byte list in hex with its SHA-256;
[check-binary](../../../scripts/check-binary) checks that functions in
binaries have exactly these bytes.

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
3. **Compare** (`hol-trace compare`): check the result against
   [accepted/](accepted) as described above; [conform.py](conform.py)
   lists the exact rules, and [accepted/README.md](accepted/README.md)
   the layout, the notation, and how each part is generated.
4. **Bind** (`check-binary`): check that the functions in binaries are the
   proved code. [../bind.yml](../bind.yml), which autogen generates from
   the accepted `.defs`, records each proved function's symbol and the
   SHA-256 of its byte list; `check-binary FILE ...` takes any ELF object,
   linked binary or archive, and compares every function whose symbol
   it names. It needs no trace.

`hol-trace check` is replay followed by compare.

The accepted files themselves are written by `hol-trace outline` (or
`scripts/autogen --hol-trace-defs`), which needs no trace: it loads each
proof with `prove` asserting each goal instead of proving it, and writes
the definitions and main theorems that result. An outline checks
nothing; review its changes, then confirm them with `gen` and `check`. See [accepted/README.md](accepted/README.md).

## What is trusted

- **Trusted:** the replay backend's kernel; `hol-trace` and
  [conform.py](conform.py), which pick and compare the theorems and
  definitions; the accepted files (see
  [accepted/README.md](accepted/README.md)); and `check-binary`.
- **Not trusted:** the proof scripts and everything else that produces
  the trace. A fault there can make a check fail, not pass.

## Usage

```bash
nix develop .#hol_trace-cross   # layers and HOL Light replay: any HOL Light shell
hol-trace list
hol-trace outline [-p FUNC ...] [--base] [--specs] [-j N]   # used by scripts/autogen --hol-trace-defs
hol-trace gen [-p FUNC ...] [--no-prune] [-j N]
hol-trace check [--backend BACKEND] [-p FUNC ...] [-j N] [--accept]
check-binary [--show-all] [--force-all] FILE ...
```

`check` is `replay` followed by `compare`; both are also available
separately, and `compare` can be rerun without replaying. As with `tests
hol_light`, each command works on one architecture: the host's, or the
one given by `--arch aarch64|x86_64`. `-p` names functions of that
architecture, such as `mlkem_ntt_aarch64_asm`; without `-p`, the
commands select all of them (see `hol-trace list`). The shared files,
which `hol-trace outline` writes without `-p` and with `--base` or
`--specs`, always cover both architectures. `hol-trace --help` lists all
options.
