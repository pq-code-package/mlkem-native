(*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 *)

(* A notation-independent prefix encoding of kernel objects, and the
   replay result format built from it.

   A replay result is "HOLTRACE-RESULT-5\n" followed by records, each a
   tag byte and its fields:

     X theorem          an axiom of the replay kernel
     D theorem          a constant definition |- c = t
     Y theorem          a type definition's |- P r = (rep (abs r) = r)
     T string theorem   a requested named theorem
     F string           failure, with a diagnostic message
     S                  end of a successful result

   A string is its byte length in decimal, ":", and its bytes. A theorem
   is the encoding below, which delimits itself. Every replay backend
   writes this format; conform.py reads it.

   What a backend must guarantee: the X records are every axiom that its
   kernel holds, and every D, Y and T theorem was returned by its kernel.
   D and Y records may be missing, since conform rejects a constant or
   type that it reaches without a definition; a missing X record would
   go unnoticed. *)

module Hol_trace_term = struct
  let raw b s =
    Buffer.add_string b (string_of_int (String.length s));
    Buffer.add_char b ':';
    Buffer.add_string b s

  let count b n =
    Buffer.add_string b (string_of_int n);
    Buffer.add_char b ':'

  let rec add_type b =
    function
    | Tyvar name ->
        Buffer.add_char b 'v';
        raw b name
    | Tyapp (name,args) ->
        Buffer.add_char b 't';
        raw b name;
        count b (length args);
        List.iter (add_type b) args

  let rec add_term b =
    function
    | Var (name,ty) ->
        Buffer.add_char b 'v';
        raw b name;
        add_type b ty
    | Const (name,ty) ->
        Buffer.add_char b 'c';
        raw b name;
        add_type b ty
    | Comb (l,r) ->
        Buffer.add_char b 'a';
        add_term b l;
        add_term b r
    | Abs (v,t) ->
        Buffer.add_char b 'l';
        add_term b v;
        add_term b t

  let theorem th =
    let hs,c = dest_thm th in
    let b = Buffer.create 256 in
    Buffer.add_char b 'h';
    count b (length hs);
    List.iter (add_term b) hs;
    add_term b c;
    Buffer.contents b

  (* holtrace_typedef_thms() lists the two theorems of every type
     definition as rth::ath::(older definitions). Keep rth,
     |- P r = (rep(abs r) = r): it determines the type definition. *)
  let rec typedef_reps =
    function
    | rth :: _ :: rest -> rth :: typedef_reps rest
    | [] -> []
    | [_] -> failwith "odd number of type-definition theorems"

  (* The records of a replay result (see the top of this file) for the
     current kernel state and the given named theorems, ending in S. The
     X records are the kernel's axioms unless ~axioms gives others:
     `hol-trace outline` asserts theorems with new_axiom and writes only
     the axioms from before it did. *)
  let theory ?axioms:(ax = axioms()) named =
    let b = Buffer.create (1 lsl 20) in
    let record tag th =
      Buffer.add_char b tag;
      Buffer.add_string b (theorem th) in
    List.iter (record 'X') ax;
    List.iter (record 'D') (definitions());
    List.iter (record 'Y') (typedef_reps (holtrace_typedef_thms()));
    List.iter (fun (name,th) ->
        Buffer.add_char b 'T';
        raw b name;
        Buffer.add_string b (theorem th))
      named;
    Buffer.add_char b 'S';
    Buffer.contents b

  let header = "HOLTRACE-RESULT-5\n"

  let write_result file records =
    let oc = open_out_bin file in
    output_string oc header;
    output_string oc records;
    close_out oc

  let write_theory ?axioms file named =
    write_result file (theory ?axioms named)

  (* A result that holds only an F record with the given message. *)
  let write_failure file msg =
    let b = Buffer.create 256 in
    Buffer.add_char b 'F';
    raw b msg;
    write_result file (Buffer.contents b)
end;;
