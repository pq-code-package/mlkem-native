(*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 *)

(* ========================================================================= *)
(* Print the loads of a proof script, one per line in load order, as        *)
(* FROM<tab>PATH<tab>FILE: the file FROM has a statement `needs "PATH"` (or  *)
(* `loadt`, `loads`), which the loader resolves to FILE. The first line,     *)
(* with FROM and PATH empty, is the script itself. Every load statement      *)
(* reached is printed, transitively; a file loaded before is not followed    *)
(* again, as `needs` loads it only once.                                     *)
(*                                                                           *)
(* This follows HOL Light's inliner, inline_load.ml, which build-proof.sh    *)
(* uses to compile every proof: the same statement syntax, resolved by the   *)
(* same loader (hol_loader.ml: load path, `needs` loading a file once). A    *)
(* load that the inliner cannot see, such as `loadt ("a" ^ "b")`, fails in   *)
(* the compiled proof, so a proof that runs loads only files printed here.   *)
(* No proof code is evaluated.                                               *)
(*                                                                           *)
(* Usage: ocaml -I "$HOLDIR" hol_deps.ml FILE.ml, in the directory and with *)
(* the load path that build-proof.sh gives the inliner. See deps here.      *)
(* ========================================================================= *)

#use "hol_loader.ml";;

(* `needs` reports files loaded before on the standard formatter. *)
Format.set_formatter_out_channel stderr;;

(* As in inline_load.ml. *)
let parse_load_statement fnname stmt: (string * string) option =
  let stmt = String.trim stmt in
  if not (String.starts_with ~prefix:fnname stmt) then None else
  let n = String.length fnname in
  let stmt = String.trim (String.sub stmt n (String.length stmt - n)) in
  if not (stmt.[0] = '"') then None else
  let stmt = String.sub stmt 1 (String.length stmt - 1) in
  let idx = String.index stmt '"' in
  if idx = -1 then None else
  let path = String.sub stmt 0 idx in
  let stmt = String.sub stmt (idx + 1) (String.length stmt - idx - 1) in
  let stmt = String.trim stmt in
  if not (String.starts_with ~prefix:";;" stmt) then None else
  let stmt = String.sub stmt 2 (String.length stmt - 2) in
  Some (path,stmt);;

let strings_of_file filename =
  let fd =
    try open_in filename
    with Sys_error _ -> failwith("strings_of_file: can't open "^filename) in
  let rec suck_lines acc =
    let l = try [input_line fd] with End_of_file -> [] in
     if l = [] then List.rev acc else suck_lines(List.hd l::acc) in
  let data = suck_lines [] in
  (close_in fd; data);;

(* Called by the loader for each file it resolves; following the file's  *)
(* load statements calls the loader again, so this recurses.              *)
let print_load from path file =
  print_endline (String.concat "\t" [from; path; file]);;

file_loader := fun filename ->
  let fail_if_nonexistent f x = try f x with _ -> failwith x in
  (* Resolve as the loader does, then load. *)
  let follow load dirs path =
    let file = fail_if_nonexistent (file_on_path dirs) path in
    print_load filename path file;
    fail_if_nonexistent load path in
  List.iter
    (fun line ->
      match parse_load_statement "loadt" line with
      | Some (path, _) -> follow loadt !load_path path
      | None ->
      match parse_load_statement "loads" line with
      | Some (path, _) ->
          (* inline_load.ml omits this one *)
          if path <> "update_database.ml" then follow loads ["$"] path
      | None ->
      match parse_load_statement "needs" line with
      | Some (path, _) -> follow needs !load_path path
      | None -> ())
    (strings_of_file filename);
  true;;

print_load "" "" (file_on_path !load_path Sys.argv.(1));;
loadt Sys.argv.(1);;
