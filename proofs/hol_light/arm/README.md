[//]: # (SPDX-License-Identifier: CC-BY-4.0)

# HOL Light functional correctness proofs

This directory contains functional correctness proofs for all AArch64 assembly routines
used in mlkem-native. The proofs were largely developed by John Harrison
and are written in the [HOL Light](https://hol-light.github.io/) theorem
prover, utilizing the assembly verification infrastructure from [s2n-bignum](https://github.com/awslabs/s2n-bignum).

Each function is proved in a separate `.ml` file in [proofs/](proofs). Each file
contains the byte code being verified, as well as the specification that is being
proved.

## Primer

Proofs are 'post-hoc' in the sense that HOL-Light/s2n-bignum operate on the final object code. In particular, the means by which the code was generated (including the [SLOTHY](https://github.com/slothy-optimizer/slothy/) superoptimizer) need not be trusted.

Specifications are essentially [Hoare triples](https://en.wikipedia.org/wiki/Hoare_logic), with the noteworthy difference that the program is implicit as the content of memory at the PC; which is asserted to
be the code under verification as part of the precondition. For example, the following is the specification of the `poly_reduce` function:

```ocaml
 (* For all (abbreviated by `!` in HOL):
    - a: Source pointer
    - pc: Current value of Program Counter (PC)
    - returnaddress: Return address in the link register *)
`!a x pc returnaddress.
    (* Assume that the program and the source pointer don't overlap *)
    nonoverlapping (word pc,0x124) (a,512)
    ==> ensures arm
      (* Precondition *)
      (\s. (* The memory at the current PC is the byte-code of poly_reduce() *)
        aligned_bytes_loaded s (word pc) mlkem_poly_reduce_mc /\
        read PC s = word pc /\
        (* The return address is stored in the link register (LR) *)
        read X30 s = returnaddress /\
        (* The source pointer is in X0 *)
        C_ARGUMENTS [a] s /\
        (* Give a name to the memory contents at the source pointer *)
        !i. i < 256
            ==> read(memory :> bytes16(word_add a (word(2 * i)))) s = x i)
      (* Postcondition: Eventually we reach a state where ... *)
      (\s.
        (* The PC is the original value of the link register *)
        read PC s = returnaddress /\
        (* The integers represented by the final memory contents
         * are the unsigned canonical reductions mod 3329
         * of the integers represented by the original memory contents. *)
        !i. i < 256
            ==> ival(read(memory :> bytes16 (word_add a (word(2 * i)))) s) =
                ival(x i) rem &3329)
      (* Footprint: The program may modify (only) the ABI permitted registers
       * and flags, and the memory contents at the source pointer. *)
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [memory :> bytes(a,512)])`
```

## Reproducing the proofs

To reproduce the proofs, enter the nix shell via

```bash
nix develop --experimental-features 'nix-command flakes'
```

from mlkem-native's base directory. Then

```bash
make -C proofs/hol_light/arm
```

will build and run the proofs. Note that this make take hours even on powerful machines.

For convenience, you can also use `tests hol_light` which wraps the `make` invocation above; see `tests hol_light --help`.

## What is covered?

All AArch64 assembly routines used in mlkem-native are covered. Those are:

- ML-KEM Arithmetic:
  * AArch64 forward NTT: [mlkem_ntt.S](mlkem/mlkem_ntt.S)
  * AArch64 inverse NTT: [mlkem_intt.S](mlkem/mlkem_intt.S)
  * AArch64 base multiplications: [mlkem_poly_basemul_acc_montgomery_cached_k2.S](mlkem/mlkem_poly_basemul_acc_montgomery_cached_k2.S) [mlkem_poly_basemul_acc_montgomery_cached_k3.S](mlkem/mlkem_poly_basemul_acc_montgomery_cached_k3.S) [mlkem_poly_basemul_acc_montgomery_cached_k4.S](mlkem/mlkem_poly_basemul_acc_montgomery_cached_k4.S)
  * AArch64 conversion to Montgomery form: [mlkem_poly_tomont.S](mlkem/mlkem_poly_tomont.S)
  * AArch64 modular reduction: [mlkem_poly_reduce.S](mlkem/mlkem_poly_reduce.S)
  * AArch64 'multiplication cache' computation: [mlkem_poly_mulcache_compute.S](mlkem/mlkem_poly_mulcache_compute.S)
  * AArch64 rejection sampling: [mlkem_rej_uniform.S](mlkem/mlkem_rej_uniform.S)
  * AArch64 polynomial compresseion: [mlkem_poly_tobytes.S](mlkem/mlkem_poly_tobytes.S)
- FIPS202:
  * Keccak-F1600 using lazy rotations[^HYBRID]: [keccak_f1600_x1_scalar.S](mlkem/keccak_f1600_x1_scalar.S)
  * Keccak-F1600 using v8.4-A SHA3 instructions: [keccak_f1600_x1_v84a.S](mlkem/keccak_f1600_x1_v84a.S)
  * 2-fold Keccak-F1600 using v8.4-A SHA3 instructions: [keccak_f1600_x2_v84a.S](mlkem/keccak_f1600_x2_v84a.S)
  * 'Hybrid' 4-fold Keccak-F1600 using scalar and v8-A Neon instructions: [keccak_f1600_x4_v8a_scalar.S](mlkem/keccak_f1600_x4_v8a_scalar.S)
  * 'Triple hybrid' 4-fold Keccak-F1600 using scalar, v8-A Neon and v8.4-A+SHA3 Neon instructions:[keccak_f1600_x4_v8a_v84a_scalar.S](mlkem/keccak_f1600_x4_v8a_v84a_scalar.S)

The NTT and invNTT functions are super-optimized using [SLOTHY](https://github.com/slothy-optimizer/slothy/).

<!--- bibliography --->
[^HYBRID]: Becker, Kannwischer: Hybrid scalar/vector implementations of Keccak and SPHINCS+ on AArch64, [https://eprint.iacr.org/2022/1243](https://eprint.iacr.org/2022/1243)
[^SLOTHY]: Abdulrahman, Becker, Kannwischer, Klein: SLOTHY superoptimizer, [https://github.com/slothy-optimizer/slothy/](https://github.com/slothy-optimizer/slothy/)
