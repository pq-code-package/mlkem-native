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
irrelevant at the trace level. In CI, this assumes that recording cannot
change what runs after it; see "Not yet isolated" below.

HOLTrace's own check, `holtrace_restore`, runs in a session that has the
trusted libraries loaded and refuses any definition that the session
lacks. We deviate from this: replay starts from core HOL Light only, and
lets the trace make its definitions, including those of s2n-bignum and
the specifications. We then compare every definition that the main
theorems rely on with the base and spec layers of [accepted/](accepted),
generated from the pinned HOL Light and s2n-bignum and from the
specification files. A trace that defines a prelude constant
differently, without adding an axiom, thus fails.

The definitions that a proof uses beyond these layers, and its main
theorems, form the proof layer of accepted/ and must be reviewed by
hand. They include the proof's machine code, as a byte list in hex with
its SHA-256; [check-binary](../../../scripts/check-binary) checks that
functions in binaries have exactly these bytes.

## How it works

1. **Record** (`hol-trace gen`): run selected proofs under HOLTrace's
   recording build, which appends every type, term, theorem, inference
   and definition to a trace (`traces/ARCH/FUNC.50`), then prune the
   trace to what the main theorems (`ARCH/list_thms.sh`) need. This can
   take hours and over 100 GB of memory and disk per proof.
2. **Replay** (`hol-trace replay --backend hol-light|hol-lean`): replay
   the trace in a separate kernel that loads no proof code, and write the
   resulting theory to a result file. The backends are
   [restore.ml](restore.ml) for HOL Light and
   [HolTraceAdapter.lean](../../../nix/hol_lean/HolTraceAdapter.lean) for
   HolLean; [term_encoding.ml](term_encoding.ml) describes the result
   format.
3. **Compare** (`hol-trace compare`): check the result against
   [accepted/](accepted); [conform.py](conform.py) lists the rules, and
   [accepted/README.md](accepted/README.md) the layout, the notation and
   how the files are generated.
4. **Bind** (`check-binary`): check that the functions in binaries are the
   proved code. [../bind.yml](../bind.yml), which autogen generates from
   the accepted `.defs`, records each proved function's symbol and the
   SHA-256 of its byte list; `check-binary FILE ...` takes any ELF object,
   linked binary or archive, and compares every function whose symbol
   it names. It needs no trace. Building with `make CHECK_BINARY=1`,
   as `scripts/tests --check-binary` does, runs it on every library and
   binary built; see [BUILDING.md](../../../BUILDING.md).

`hol-trace check` is replay followed by compare. The accepted files are
written by `hol-trace outline`, through `scripts/autogen
--hol-trace-defs`, which needs no trace; see
[accepted/README.md](accepted/README.md).

## Changing or adding a proof

Run these from the repository root in a HOL Light nix shell:
`nix develop .#hol_light` for the host's architecture, or
`nix develop .#hol_light-cross` for both. For a proof of the other
architecture, add `--arch ARCH` to the `hol-trace` commands, as with
`tests hol_light`. Only `gen` and the HolLean backend need
`nix develop .#hol_trace-cross`.

**After editing a proof**, `ARCH/proofs/FUNC.ml` or its `.S` file:

1. Check the proof as usual, e.g. `tests hol_light -p FUNC`.
2. Rewrite its accepted files with `scripts/autogen --hol-trace-defs
   FUNC`, which also updates `proofs/hol_light/bind.yml`. If only
   tactics changed, nothing changes.
3. Review `git diff proofs/hol_light`. A change to `FUNC.thms` changes
   what the proof claims; a change to the byte list in `FUNC.defs`
   changes the code that it is about.
4. If the code changed, check the object file:
   `make -B -C proofs/hol_light/ARCH mlkem/FUNC.o`, then
   `check-binary proofs/hol_light/ARCH/mlkem/FUNC.o`.
5. Commit the accepted files with the proof. CI records and replays the
   proof, and fails if the accepted files do not match.

**After editing a specification file**, that is a file in `common/` or a
file in `ARCH/proofs/` that is not a proof, **or after updating HOL Light
or s2n-bignum**: run `scripts/autogen --hol-trace-defs`, which rewrites
the shared files and every proof's files. Review `accepted/spec`
carefully, since it holds the specifications; changes to `accepted/base`
should be explained by the update.

**When adding a proof**, in addition to the usual HOL Light steps, name
its main theorems as `ARCH/list_thms.sh` derives them from the routine
name (lint checks this), and run
`scripts/autogen --hol-trace-defs FUNC`. It writes the proof's accepted
files and adds the proof to [proofs/hol_light/deps.yml](../deps.yml),
from which CI selects the proofs to check, and to
[proofs/hol_light/bind.yml](../bind.yml). If it reports entries that
would be stored as hashes, find out where they come from before running
`hol-trace outline --accept-hashed`.

An outline only writes files; it proves nothing. To run CI's check
yourself, use `hol-trace gen -p FUNC` and then
`hol-trace check -p FUNC`.

## What is trusted

- **Trusted:** the replay backend's kernel; `hol-trace` and
  [conform.py](conform.py), which pick and compare the theorems and
  definitions; the accepted files (see
  [accepted/README.md](accepted/README.md)); and `check-binary`.
- **Not trusted:** the proof scripts and everything else that produces
  the trace. A fault there can make a check fail, not pass.
- **Not yet isolated:** `gen` runs the proof scripts on the same CI
  runner as the checks after it, so a reviewer must check that a proof
  script only drives HOL Light.

## Usage

```bash
nix develop .#hol_light          # outline and HOL Light replay; gen and HolLean: .#hol_trace-cross
hol-trace list
hol-trace outline [--base] [--specs] [-p FUNC ...] [--out DIR] [-j N]
hol-trace gen [-p FUNC ...] [--no-prune] [-j N]
hol-trace check [--backend BACKEND] [-p FUNC ...] [-j N] [--accept]
check-binary [--show-all] [--force-all] FILE ...
```

Each command works on the proofs of one architecture, the host's or
`--arch`'s; `-p` selects functions (see `hol-trace list`), also of the
other architecture as `ARCH/FUNC`.
`hol-trace --help` and `check-binary --help` list all options.
