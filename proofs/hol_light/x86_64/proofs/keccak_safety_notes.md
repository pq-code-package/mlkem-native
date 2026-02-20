# Keccak f1600 x4 AVX2 - Safety Proof Notes

## Overview

After the correctness proof is committed (with standard stack frame), add
constant-time and memory safety proofs following the three-level pattern.

## Prerequisites

1. Add entry to `subroutine_signatures.ml`:

```ocaml
("keccak_f1600_x4_avx2",
  ([(*args*)
     ("states", "uint64_t[static 100]", (*is const?*)"false");
     ("rc", "uint64_t[static 24]", (*is const?*)"true");
     ("rho8", "uint64_t[static 4]", (*is const?*)"true");
     ("rho56", "uint64_t[static 4]", (*is const?*)"true");
   ],
   "void",
   [(* input buffers *)
    ("states", "100"(* num elems *), 8(* elem bytesize *));
    ("rc", "24"(* num elems *), 8(* elem bytesize *));
    ("rho8", "4"(* num elems *), 8(* elem bytesize *));
    ("rho56", "4"(* num elems *), 8(* elem bytesize *));
   ],
   [(* output buffers *)
    ("states", "100"(* num elems *), 8(* elem bytesize *));
   ],
   [(* temporary buffers *)
   ])
);
```

Names match C header in `dev/fips202/x86_64/src/fips202_native_x86_64.h`:
```c
void mlk_keccak_f1600_x4_avx2(uint64_t states[100], const uint64_t rc[24],
                              const uint64_t rho8[4], const uint64_t rho56[4])
```

## Safety Proof Structure

Append to `keccak_f1600_x4_avx2.ml` after SUBROUTINE_CORRECT.

### Step 1: Generate safety spec from core CORRECT

```ocaml
needs "x86_64/proofs/mlkem_utils.ml";;
needs "x86_64/proofs/subroutine_signatures.ml";;

let full_spec,public_vars = mk_safety_spec
    ~keep_maychanges:true
    (assoc "keccak_f1600_x4_avx2" subroutine_signatures)
    KECCAK_F1600_X4_AVX2_CORRECT
    KECCAK_F1600_X4_AVX2_EXEC;;
```

May need dedup/simplification like mlkem_ntt.ml:
```ocaml
let full_spec = LENGTH_SIMPLIFY_CONV full_spec |> concl |> rhs;;
```

### Step 2: Core SAFE proof

```ocaml
let KECCAK_F1600_X4_AVX2_SAFE = time prove
 (full_spec,
  ASSERT_CONCL_TAC full_spec THEN
  CONV_TAC LENGTH_SIMPLIFY_CONV THEN
  PROVE_SAFETY_SPEC_TAC ~public_vars:public_vars KECCAK_F1600_X4_AVX2_EXEC);;
```

### Step 3: NOIBT_SUBROUTINE_SAFE (stack promotion)

Uses `X86_PROMOTE_RETURN_STACK_TAC` since the function has a standard stack
frame (sub rsp,0x300 / add rsp,0x300) with no saved callee-saved registers.

```ocaml
let KECCAK_F1600_X4_AVX2_NOIBT_SUBROUTINE_SAFE = time prove
 (<goal needs to be written explicitly or generated>,
  X86_PROMOTE_RETURN_STACK_TAC
   keccak_f1600_x4_avx2_tmc
   (CONV_RULE LENGTH_SIMPLIFY_CONV KECCAK_F1600_X4_AVX2_SAFE)
   `[]` 768 THEN DISCHARGE_SAFETY_PROPERTY_TAC);;
```

Key parameters:
- `[]` = no callee-saved registers pushed
- `768` = stack allocation size (0x300)
- Stack region: `word_sub stackpointer (word 0x300)` for 0x300 bytes
- With return address: total 0x308 bytes

### Step 4: SUBROUTINE_SAFE (IBT rule)

```ocaml
let KECCAK_F1600_X4_AVX2_SUBROUTINE_SAFE = time prove
 (<same goal but with mc instead of tmc>,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE KECCAK_F1600_X4_AVX2_NOIBT_SUBROUTINE_SAFE));;
```

## Reference Files

- **Stack safety pattern**: s2n-bignum `x86/proofs/bignum_montmul_p256.ml` lines 620-726
- **No-stack safety pattern**: `mlkem_poly_compress_d4.ml` lines 480-582
- **Dedup pattern**: `mlkem_ntt.ml` lines 1293-1305
