[//]: # (SPDX-License-Identifier: CC-BY-4.0)

CBMC proofs
===========

This directory contains the infrastructure for running [CBMC](https://github.com/diffblue/cbmc) proofs
for the absence of certain classes of undefined behaviour for parts of the C-code in mlkem-native.

## Primer

Proofs are organized by functions, with the harnesses for each function in a separate directory.
Specifications are directly embedded inside the mlkem-native C-source as contract and loop annotations;
the CBMC harnesses are boilerplate only and don't add to the specification.

For example, these are the specification and proof of the `poly_add` function:
```c
void mlk_poly_add(mlk_poly *r, const mlk_poly *b)
__contract__(
  requires(memory_no_alias(r, sizeof(mlk_poly)))
  requires(memory_no_alias(b, sizeof(mlk_poly)))
  requires(forall(k0, 0, MLKEM_N, (int32_t) r->coeffs[k0] + b->coeffs[k0] <= INT16_MAX))
  requires(forall(k1, 0, MLKEM_N, (int32_t) r->coeffs[k1] + b->coeffs[k1] >= INT16_MIN))
  ensures(forall(k, 0, MLKEM_N, r->coeffs[k] == old(*r).coeffs[k] + b->coeffs[k]))
  assigns(memory_slice(r, sizeof(mlk_poly)))
);

...

void mlk_poly_add(mlk_poly *r, const mlk_poly *b)
{
  unsigned i;
  for (i = 0; i < MLKEM_N; i++)
  __loop__(
    invariant(i <= MLKEM_N)
    invariant(forall(k0, i, MLKEM_N, r->coeffs[k0] == loop_entry(*r).coeffs[k0]))
    invariant(forall(k1, 0, i, r->coeffs[k1] == loop_entry(*r).coeffs[k1] + b->coeffs[k1])))
  {
    r->coeffs[i] = r->coeffs[i] + b->coeffs[i];
  }
}
```

See the [Proof Guide](proof_guide.md) for a walkthrough of how to use CBMC and develop new proofs.

## Reproducing the proofs

To run all proofs, print a summary at the end and reflect overall
success/failure in the error code, use

```
MLKEM_K={2,3,4} run-cbmc-proofs.py --summarize
```

If `GITHUB_STEP_SUMMARY` is set, the proof summary will be appended to it.

Alternatively, you can use the [tests](../../scripts/tests) script, see

```
tests cbmc --help
```

## What is covered?

Each proved function has an eponymous sub-directory of its own. Use [list_proofs.sh](list_proofs.sh) to see the list of functions covered.
