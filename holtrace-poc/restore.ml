(*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 *)

(* ========================================================================= *)
(* TEMPORARY PoC: replay a HOLTrace file through a fresh HOL Light kernel.   *)
(*                                                                           *)
(* This process loads only core HOL Light (hol_lib) plus holtrace.ml. None   *)
(* of the s2n-bignum or mlkem-native OCaml code runs here: every theorem is  *)
(* rebuilt by replaying the recorded primitive inferences through the        *)
(* kernel (fusion.ml) of this process.                                       *)
(*                                                                           *)
(* Inputs (environment):                                                     *)
(*   HOLTRACE_RESTORE  trace file                                            *)
(*   HOLTRACE_NAMES    file with one theorem name per line                   *)
(*                                                                           *)
(* Policy: new constant and type definitions are accepted (they are          *)
(* conservative), new axioms are rejected, and every recorded theorem        *)
(* statement must match the replayed theorem exactly.                        *)
(* ========================================================================= *)

let restore_trace = Sys.getenv "HOLTRACE_RESTORE";;
let restore_names =
  let ic = open_in (Sys.getenv "HOLTRACE_NAMES") in
  let rec go acc =
    match In_channel.input_line ic with
    | None -> close_in ic; rev acc
    | Some l -> go (if String.trim l = "" then acc else String.trim l :: acc) in
  go [];;

let restore_axioms_before = axioms();;

holtrace_restore_worker Sys.time
  false (* allownewaxioms *)
  true  (* allownewdefs *)
  true  (* checkthmstatements *)
  [] restore_trace;;

if axioms() <> restore_axioms_before then failwith "restore: axioms changed";;

Printf.printf "RESTORE axioms: %d\n" (length (axioms()));;
Printf.printf "RESTORE definitions: %d\n" (length (definitions()));;
Printf.printf "RESTORE constants: %d\n" (length (constants()));;
Printf.printf "RESTORE types: %d\n%!" (length (types()));;

List.iter (fun n ->
    let th = holtrace_restore_name2thm n in
    let asl,_ = dest_thm th in
    Printf.printf "RESTORED %s (hyps: %d)\n%s\n\n%!" n (length asl)
      (string_of_thm th))
  restore_names;;

Printf.printf "RESTORE OK\n%!";;
