[//]: # (SPDX-License-Identifier: CC-BY-4.0)

# Proofs for mlkem-native

This directory contains material related to the formal verification of the source code of mlkem-native.

## C verification: CBMC

We use the [C Bounded Model Checker (CBMC)](https://github.com/diffblue/cbmc) to show the absence of various classes of undefined behaviour in the mlkem-native C source, including out of bounds memory accesses and integer overflows. See [proofs/cbmc](cbmc).

## Assembly verification: HOL-Light

We use the [HOL-Light](https://github.com/jrh13/hol-light) interactive theorem prover alongside the verification infrastructure from [s2n-bignum](https://github.com/awslabs/s2n-bignum) to show the functional correctness of all AArch64 assembly and all x86_64 ML-KEM arithmetic assembly in mlkem-native at the object-code level. See [proofs/hol_light](hol_light).

## C/functional verification in Isabelle (AutoCorrode)

We use [Isabelle/HOL](https://isabelle.in.tum.de/) together with [AutoCorrode](https://github.com/awslabs/AutoCorrode) to translate and verify selected C implementations and their refinement lemmas. See [proofs/isabelle](isabelle).
