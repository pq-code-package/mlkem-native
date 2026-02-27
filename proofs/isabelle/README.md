[//]: # (SPDX-License-Identifier: CC-BY-4.0)

# Isabelle proofs

This directory contains Isabelle/HOL proofs for `mlkem-native`, built on top of AutoCorrode.

## Prerequisites

- Isabelle2025-2 (`isabelle` binary available via `ISABELLE_HOME`)
- An AutoCorrode checkout (set `AUTOCORRODE_DIR`)
- AFP mirror checkout containing `Word_Lib` and `Isabelle_C` (set `AFP_COMPONENT_BASE`)

Default Makefile assumptions:

- `AUTOCORRODE_DIR=../../AutoCorrode`
- `AFP_COMPONENT_BASE=$(AUTOCORRODE_DIR)/dependencies/afp`

## Usage

From the repository root:

```bash
make -C proofs/isabelle pipeline
make -C proofs/isabelle build
make -C proofs/isabelle jedit
```

## Pipeline overview

Translation units are preprocessed from `mlkem/src/*.c` using compile flags discovered from the root Makefile.
Generated artifacts are written under `generated/`.

Useful controls:

- `PIPELINE_UNIT` (default `poly`)
- `PIPELINE_PARAMETER_SET` (default `512`)
- `PIPELINE_OPT` (default `0`)
- `PIPELINE_AUTO` (default `0`)

## Current theory split

- `Common.thy`: shared abstractions and refinement lemmas.
- `MLKEM_Machine_Model.thy`: shared machine-model locale; imports type-only extraction (`poly.types.manifest`) so generated C record types are available for reference assumptions.
- `MLKEM_Poly_Definitions.thy`: auto-generated function definitions from `poly.c`, produced inside `context c_mlk_machine_model`.
- `MLKEM_Poly_Functional_Correctness.thy`: contracts and WP proofs for generated `poly.c` definitions.
- `MLKEM_Verify_Definitions.thy`: extracted translation of `verify.c` (proofs pending).
- `MLKEM_Functional_Correctness.thy`: top-level aggregation theory.
