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
change what runs after it; see the caveat "Not yet isolated" below.

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
nothing; review its changes, then confirm them with `gen` and `check`,
as CI does. See [accepted/README.md](accepted/README.md).

## Changing or adding a proof

Run these from the repository root in a HOL Light nix shell:
`nix develop .#hol_light` for the host's architecture, or
`nix develop .#hol_light-cross` for both. For a proof of the other
architecture, add `--arch ARCH` to the `hol-trace` commands, as with
`tests hol_light`. Only `gen` needs
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
nix develop .#hol_trace-cross   # outline and HOL Light replay: any HOL Light shell
hol-trace list
hol-trace outline [--base] [--specs] [-p FUNC ...] [--out DIR] [-j N]   # used by scripts/autogen --hol-trace-defs
hol-trace gen [-p FUNC ...] [--no-prune] [-j N]
hol-trace check [--backend BACKEND] [-p FUNC ...] [-j N] [--accept]
check-binary [--show-all] [--force-all] FILE ...
```

`check` is `replay` followed by `compare`; both are also available
separately, and `compare` can be rerun without replaying. As with `tests
hol_light`, each command works on one architecture: the host's, or the
one given by `--arch aarch64|x86_64`. `-p` names functions of that
architecture, such as `mlkem_ntt_aarch64_asm`; without `-p`, the
commands select all of them (see `hol-trace list`). `hol-trace outline`
also takes `--base` and `--specs` for the shared files, which always
cover both architectures; these and `-p` combine, and with none of them
it writes everything. `hol-trace --help` lists all options.

## CI

[hol_trace.yml](../../../.github/workflows/hol_trace.yml) runs in the
upstream repository and skips fork pull requests. Manual dispatch checks
all proofs.

A hosted runner selects the affected proofs before starting an
instance, with `proofs/hol_light/scripts/deps rev` from
[proofs/hol_light/deps.yml](../deps.yml), exactly as HOL-Light CI
does. An empty selection skips EC2 provisioning.

One temporary `r9g.24xlarge` runner with a 512 GB disk checks the entire
selection; there is no EC2 proof matrix. The ARM64 runner
cross-assembles x86_64 proofs in `nix develop .#hol_trace-cross`.
It sets a 1 GiB stack and uses eight workers for each phase. Each phase
is a step of its own, so the job's log shows them separately:
1. capture traces of every selected proof (`gen`);
2. replay them with HOL Light;
3. compare every replay result with the accepted files;
4. check the proofs' object files with `check-binary --force-all`: each
   must contain only proved functions, with the proved bytes.

Each phase finishes for all proofs before the next starts, and runs
`hol-trace` once per architecture. Comparisons use eight separate
processes. Other proofs and later phases continue if one fails, and any
failure fails the job. Traces and replay results are removed after all
checks finish. CI never accepts new definitions or statements.
Generation and replay logs and manifests are retained for seven days;
the large trace files are not uploaded. The job has a 24-hour timeout.
The existing EC2 workflow stops the runner after the job, including on
failure or cancellation.
