[//]: # (SPDX-License-Identifier: CC-BY-4.0)

CBMC proofs
===========

# Overview

This directory contains [CBMC](https://github.com/diffblue/cbmc) proofs for the absence
of certain classes of undefined behaviour for parts of the C-code in mlkem-native.

Proofs are organized by functions, with the harnesses and proofs for each function
in a separate directory.

See the [Proof Guide](proof_guide.md) for a walkthrough of how to use CBMC and
develop new proofs.

# Usage

To run all proofs, print a summary at the end and reflect overall
success/failure in the error code, use

```
MLKEM_K={2,3,4} run-cbmc-proofs.py --summarize
```

If `GITHUB_STEP_SUMMARY` is set, the proof summary will be appended to it.

# Covered functions

Each proved function has an eponymous sub-directory of its own. The shell command

```
find . -name cbmc-proof.txt
```

yields a list of the subdirectories, and thus function names, that have a proof.
