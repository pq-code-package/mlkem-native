(*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 *)

(* ========================================================================= *)
(* TEMPORARY PoC attack: prove a true theorem that reads as a false one.     *)
(*                                                                           *)
(* The kernel is not fooled here. The parser and printer are: earlier OCaml  *)
(* code remaps `+` to another constant, so both the source text `2 + 2 = 5`  *)
(* and the printed theorem look like a false claim about addition. In a     *)
(* real attack the remapping would sit deep in a shared library and target  *)
(* a symbol such as `rem` or `word_add` in a specification.                 *)
(* ========================================================================= *)

let fake_add = new_definition `fake_add (m:num) (n:num) = m + n + 1`;;

overload_interface ("+", `fake_add:num->num->num`);;

let MLKEM_ATTACK_SPOOF = prove
 (`2 + 2 = 5`,
  REWRITE_TAC[fake_add] THEN ARITH_TAC);;

print_endline ("Proof process shows: " ^ string_of_thm MLKEM_ATTACK_SPOOF);;
