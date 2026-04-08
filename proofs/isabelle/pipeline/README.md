[//]: # (SPDX-License-Identifier: CC-BY-4.0)

# Isabelle pipeline (C -> preprocessed C -> theory)

This directory contains the source-driven generation pipeline for `proofs/isabelle`.

## Configured units

- `mlkem/src/poly.c` -> `generated/c/poly.pre.c` -> `MLKEM_Poly_Definitions.thy`
- `mlkem/src/verify.c` -> `generated/c/verify.pre.c` -> `MLKEM_Verify_Definitions.thy`

## Driver

Use `pipeline/generate.py`.
It queries the root `Makefile` for compile flags, extracts preprocessor-relevant flags,
and runs preprocessing.

From `proofs/isabelle`:

```bash
make pipeline
make pipeline-flags
make pipeline-correctness
```

To regenerate a single unit:

```bash
make pipeline PIPELINE_UNIT=poly
make pipeline PIPELINE_UNIT=verify
```

## Filtering layers

Filtering is split intentionally:

- `extract` (in `units.json`): script-level trimming of preprocessed C before Isabelle parsing.
- `manifest` (in `units.json`): declarative function/type filtering passed to `micro_c_file`.
- `type_manifest` (optional, in `units.json`): emits a type-only manifest used for two-phase translation.

For `poly`, the flow is:

1. `MLKEM_Machine_Model.thy` runs `micro_c_file` with `generated/manifests/poly.types.manifest`
   to declare required C-derived types (for example `c_mlk_poly`).
2. `MLKEM_Poly_Definitions.thy` runs `micro_c_file` with `generated/manifests/poly.functions.manifest`
   inside `context c_mlk_machine_model` to generate function definitions.

## Manifest format

Manifest files are plain text with optional `functions:` and `types:` sections.
Entries can be bare names or `-`-prefixed names:

```text
functions:
- mlk_barrett_reduce
- mlk_poly_add

types:
- mlk_poly
- int16_t
```
