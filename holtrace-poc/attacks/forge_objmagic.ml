(*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 *)

(* ========================================================================= *)
(* TEMPORARY PoC attack: forge a theorem by casting an OCaml value to `thm`. *)
(*                                                                           *)
(* HOL Light's soundness rests on `thm` being abstract: only the kernel can  *)
(* build one. Obj.magic (or Marshal, or a memory-corruption bug in OCaml, a  *)
(* C stub, or the compiler) breaks that abstraction inside the proof process.*)
(* The proof process itself cannot notice.                                   *)
(* ========================================================================= *)

let FORGED_FALSE : thm = Obj.magic (Some ((([]:term list)), `F`));;

let MLKEM_ATTACK_FORGED = prove
 (`1 = 2`,
  ACCEPT_TAC(CONTR `1 = 2` FORGED_FALSE));;

print_endline ("Proof process shows: " ^ string_of_thm MLKEM_ATTACK_FORGED);;
