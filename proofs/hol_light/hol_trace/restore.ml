(*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 *)

(* ========================================================================= *)
(* Replay a HOLTrace trace through this process's kernel and dump the        *)
(* resulting theory.                                                         *)
(*                                                                           *)
(* Built by `hol-trace replay` against the replay HOL Light (plain HOLTrace  *)
(* install, unchanged kernel). This process loads core HOL Light,            *)
(* holtrace.ml and the term encoder: no s2n-bignum or proof code.            *)
(*                                                                           *)
(* HOLTrace's replay refuses new axioms and checks every recorded theorem    *)
(* statement against the rebuilt theorem. By default it also refuses         *)
(* definitions that the session does not already have; this file allows      *)
(* them (allownewdefs), since it loads no s2n-bignum or specification        *)
(* files, and applies no further policy: it writes the kernel's axioms,      *)
(* constant definitions and type definitions, and the requested named        *)
(* theorems. `hol-trace compare` decides whether they are acceptable.        *)
(*                                                                           *)
(* Environment:                                                              *)
(*   HOLTRACE_TRACE       trace file                                         *)
(*   HOLTRACE_NAMES       file with one theorem name per line                *)
(*   HOLTRACE_RESULT      result file; format in term_encoding.ml            *)
(* ========================================================================= *)

needs "mlkem_native/hol_trace/term_encoding.ml";;

let hol_trace_result_file =
  try Sys.getenv "HOLTRACE_RESULT" with Not_found ->
    Printf.eprintf "hol_trace: HOLTRACE_RESULT not set\n%!";
    exit 1;;

let hol_trace_fail msg =
  Hol_trace_term.write_failure hol_trace_result_file msg;
  Printf.eprintf "hol_trace: %s\n%!" msg;
  exit 1;;

let hol_trace_env v =
  try Sys.getenv v with Not_found -> hol_trace_fail (v ^ " not set");;

let hol_trace_names =
  let ic = open_in (hol_trace_env "HOLTRACE_NAMES") in
  let rec go acc =
    match In_channel.input_line ic with
    | None -> close_in ic; rev acc
    | Some l -> go (if l = "" then acc else l :: acc) in
  go [];;

(* No per-line timing: Sys.time costs a getrusage(2) call per trace line.    *)
let () =
  try
    holtrace_restore_worker (fun () -> 0.0)
      false (* allownewaxioms *)
      true  (* allownewdefs *)
      true  (* checkthmstatements *)
      [] (hol_trace_env "HOLTRACE_TRACE")
  with e -> hol_trace_fail ("replay failed: " ^ Printexc.to_string e);;

let () =
  let named =
    map (fun name ->
        try name, holtrace_restore_name2thm name
        with Not_found -> hol_trace_fail ("the trace does not name " ^ name))
      hol_trace_names in
  Hol_trace_term.write_theory hol_trace_result_file named;
  Printf.printf "HOLTRACE-REPLAY OK: %d named theorems\n%!"
    (length hol_trace_names);;
