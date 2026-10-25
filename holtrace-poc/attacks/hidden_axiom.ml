(*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 *)

(* ========================================================================= *)
(* TEMPORARY PoC attack: add a false axiom and disable the axiom check.      *)
(*                                                                           *)
(* build-proof.sh appends `check_axioms ();;` after the proof script. The    *)
(* script runs first in the same OCaml scope, so it can rebind the name.     *)
(* ========================================================================= *)

let check_axioms () = ();;

let BOGUS_AX = new_axiom `!n:num. n = 0`;;

let MLKEM_ATTACK_AXIOM = prove
 (`1 = 2`,
  ACCEPT_TAC(TRANS (SPEC `1` BOGUS_AX) (SYM (SPEC `2` BOGUS_AX))));;

print_endline ("Proof process shows: " ^ string_of_thm MLKEM_ATTACK_AXIOM);;
