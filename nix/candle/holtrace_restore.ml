(*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 *)

(* Replay one compact HOLTrace entry at a time through Candle's kernel. *)

type 'a hol_trace_array = ('a array * int * 'a) ref;;

let hol_trace_array default =
  ref (Array.make 0 default,0,default);;

let hol_trace_array_length array =
  let _,length,_ = !array in length;;

let hol_trace_array_get array index =
  let data,length,_ = !array in
  if index < 0 || index >= length then failwith "bad HOLTrace object ID";
  Array.get data index;;

let hol_trace_array_add array value =
  let data,length,default = !array in
  let data = Cake.Array.updateResize data default length value in
  array := (data,length + 1,default);;

let hol_trace_printable_name name =
  let rec loop index =
    if index = String.length name then true else
    let code = Char.code name.[index] in
    code > Char.code ' ' && code <= Char.code '~' && loop (index + 1) in
  String.length name > 0 && loop 0;;

let hol_trace_identifier name =
  let first char =
    let code = Char.code char in
    (code >= Char.code 'a' && code <= Char.code 'z') ||
    (code >= Char.code 'A' && code <= Char.code 'Z') ||
    (code >= Char.code '0' && code <= Char.code '9') ||
    code = Char.code '_' in
  let rest char =
    let code = Char.code char in
    first char || code = Char.code '\'' || code = Char.code '.' in
  let rec loop index =
    if index = String.length name then true
    else rest name.[index] && loop (index + 1) in
  String.length name > 0 && first name.[0] && loop 1;;

let hol_trace_parse_name line position =
  let name = String.sub line position (String.length line - position) in
  if hol_trace_printable_name name then name
  else failwith "refusing unusual characters in trace name";;

let hol_trace_parse_subid line position reference =
  let length = String.length line in
  let rec nonnegative position result =
    if position >= length then position,result else
    let code = Char.code line.[position] in
    if code = Char.code ' ' then position + 1,result
    else if code >= Char.code '0' && code <= Char.code '9' then
      nonnegative (position + 1)
        (result * 32 + code - Char.code '0')
    else if code >= Char.code 'A' && code <= Char.code 'V' then
      nonnegative (position + 1)
        (result * 32 + code - Char.code 'A' + 10)
    else position,result in
  let allow_negative position =
    if position >= length then position,0 else
    if Char.code line.[position] = Char.code '-' then
      let position,value = nonnegative (position + 1) 0 in
      position,reference - value
    else
      let next,value = nonnegative position 0 in
      if next = position then failwith "missing HOLTrace object ID";
      next,value in
  let position,value =
    if position >= length then position,0 else
    match line.[position] with
    | '!' -> position + 1,reference - 1
    | '@' -> position + 1,reference - 2
    | '#' -> position + 1,reference - 3
    | '$' -> position + 1,reference - 4
    | '%' -> position + 1,reference - 5
    | '^' -> position + 1,reference - 6
    | '&' -> position + 1,reference - 7
    | '*' -> position + 1,reference - 8
    | '(' -> position + 1,reference - 9
    | ')' -> position + 1,reference - 10
    | _ -> allow_negative position in
  if value < 0 || (reference >= 0 && value >= reference)
  then
    failwith
      ("forward HOLTrace object ID " ^ string_of_int value ^
       " at bound " ^ string_of_int reference);
  position,value;;

let hol_trace_parse_many count line position reference =
  let rec loop count position result =
    if count <= 0 then position,rev result else
    let position,value =
      hol_trace_parse_subid line position reference in
    loop (count - 1) position (value::result) in
  loop count position [];;

let hol_trace_parse_pairs line position reference =
  let rec loop position result =
    if position = String.length line then rev result else
    let position,from_id =
      hol_trace_parse_subid line position reference in
    let position,to_id =
      hol_trace_parse_subid line position reference in
    loop position ((to_id,from_id)::result) in
  loop position [];;

let hol_trace_split separator string =
  let length = String.length string in
  let rec loop start position result =
    if position = length then
      rev (String.sub string start (position - start)::result)
    else if Char.code string.[position] = Char.code separator then
      loop (position + 1) (position + 1)
        (String.sub string start (position - start)::result)
    else loop start (position + 1) result in
  loop 0 0 [];;

type hol_trace_entry =
  | Holtrace_vartype of string
  | Holtrace_type of int list * string
  | Holtrace_const of int * string
  | Holtrace_var of int * string
  | Holtrace_comb of int * int * int
  | Holtrace_abs of int * int * int
  | Holtrace_thm of int list
  | Holtrace_name of int * string
  | Holtrace_axiom of int
  | Holtrace_beta of int
  | Holtrace_refl of int
  | Holtrace_assume of int
  | Holtrace_abs_rule of int * int
  | Holtrace_eq_mp of int * int
  | Holtrace_trans of int * int
  | Holtrace_deduct_antisym of int * int
  | Holtrace_mk_comb of int * int
  | Holtrace_inst of int * (int * int) list
  | Holtrace_inst_type of int * (int * int) list
  | Holtrace_definition of int * string
  | Holtrace_typedef of
      int * int * int * string * string * string * string list
  | Holtrace_typedef_followup of int
  | Holtrace_ignore;;

let hol_trace_decode type_count term_count thm_count typedef_count line =
  if String.length line = 0 then failwith "blank HOLTrace line";
  let one reference =
    let position,value = hol_trace_parse_subid line 1 reference in
    if position <> String.length line then failwith "trailing HOLTrace input";
    value in
  let two reference =
    let position,left = hol_trace_parse_subid line 1 reference in
    let position,right = hol_trace_parse_subid line position reference in
    if position <> String.length line then failwith "trailing HOLTrace input";
    left,right in
  match line.[0] with
  | 'a' -> Holtrace_vartype(hol_trace_parse_name line 1)
  | 'b' ->
      let position,count = hol_trace_parse_subid line 1 (-1) in
      let position,args =
        hol_trace_parse_many count line position type_count in
      Holtrace_type(args,hol_trace_parse_name line position)
  | 'c' ->
      let position,ty = hol_trace_parse_subid line 1 type_count in
      Holtrace_const(ty,hol_trace_parse_name line position)
  | 'd' ->
      let position,ty = hol_trace_parse_subid line 1 type_count in
      Holtrace_var(ty,hol_trace_parse_name line position)
  | 'e' ->
      let position,ty = hol_trace_parse_subid line 1 type_count in
      let position,left = hol_trace_parse_subid line position term_count in
      let position,right = hol_trace_parse_subid line position term_count in
      if position <> String.length line then failwith "trailing HOLTrace input";
      Holtrace_comb(ty,left,right)
  | 'f' ->
      let position,ty = hol_trace_parse_subid line 1 type_count in
      let position,var = hol_trace_parse_subid line position term_count in
      let position,body = hol_trace_parse_subid line position term_count in
      if position <> String.length line then failwith "trailing HOLTrace input";
      Holtrace_abs(ty,var,body)
  | 't' ->
      let rec loop position result =
        if position = String.length line then result else
        let position,value =
          hol_trace_parse_subid line position term_count in
        loop position (value::result) in
      Holtrace_thm(loop 1 [])
  | '/' ->
      let position,id = hol_trace_parse_subid line 1 thm_count in
      Holtrace_name(id,hol_trace_parse_name line position)
  | 'X' -> Holtrace_axiom(one term_count)
  | 'B' -> Holtrace_beta(one term_count)
  | 'R' -> Holtrace_refl(one term_count)
  | 'U' -> Holtrace_assume(one term_count)
  | 'F' ->
      let position,term_id = hol_trace_parse_subid line 1 term_count in
      let position,thm_id = hol_trace_parse_subid line position thm_count in
      if position <> String.length line then failwith "trailing HOLTrace input";
      Holtrace_abs_rule(term_id,thm_id)
  | 'P' -> let left,right = two thm_count in Holtrace_eq_mp(left,right)
  | 'V' -> let left,right = two thm_count in Holtrace_trans(left,right)
  | 'Z' ->
      let left,right = two thm_count in
      Holtrace_deduct_antisym(left,right)
  | 'E' -> let left,right = two thm_count in Holtrace_mk_comb(left,right)
  | 'S' ->
      let position,id = hol_trace_parse_subid line 1 thm_count in
      Holtrace_inst(id,hol_trace_parse_pairs line position term_count)
  | 'T' ->
      let position,id = hol_trace_parse_subid line 1 thm_count in
      Holtrace_inst_type(id,hol_trace_parse_pairs line position type_count)
  | 'C' ->
      let position,id = hol_trace_parse_subid line 1 term_count in
      Holtrace_definition(id,hol_trace_parse_name line position)
  | 'A' ->
      let position,reptype = hol_trace_parse_subid line 1 type_count in
      let position,repprop = hol_trace_parse_subid line position term_count in
      let position,repth = hol_trace_parse_subid line position thm_count in
      let word = hol_trace_parse_name line position in
      let parts = hol_trace_split ']' word in
      (match parts with
       | ""::tyname::absname::repname::tyvars ->
           if hd(rev tyvars) <> "" then
             failwith "bad HOLTrace type-definition names";
           Holtrace_typedef
             (reptype,repprop,repth,tyname,absname,repname,
              rev(tl(rev tyvars)))
       | _ -> failwith "bad HOLTrace type-definition names")
  | 'D' -> Holtrace_typedef_followup(one typedef_count)
  | ',' | ';' -> Holtrace_ignore
  | tag -> failwith ("unknown HOLTrace tag " ^ String.make 1 tag);;

let hol_trace_default_term = mk_const("=",[]);;
let hol_trace_default_thm = REFL hol_trace_default_term;;
let hol_trace_types = hol_trace_array bool_ty;;
let hol_trace_terms = hol_trace_array hol_trace_default_term;;
let hol_trace_thms = hol_trace_array hol_trace_default_thm;;
let hol_trace_typedefs = hol_trace_array hol_trace_default_thm;;
let hol_trace_last = ref hol_trace_default_thm;;
let hol_trace_has_last = ref false;;
let hol_trace_names = ref ([]:(string * thm) list);;
let hol_trace_definitions = ref ([]:thm list);;

let hol_trace_infer th =
  hol_trace_last := th;
  hol_trace_has_last := true;;

let hol_trace_replay =
  function
  | Holtrace_vartype name ->
      hol_trace_array_add hol_trace_types (mk_vartype name)
  | Holtrace_type(args,name) ->
      hol_trace_array_add hol_trace_types
        (mk_type(name,map (hol_trace_array_get hol_trace_types) args))
  | Holtrace_const(ty,name) ->
      hol_trace_array_add hol_trace_terms
        (mk_mconst(name,hol_trace_array_get hol_trace_types ty))
  | Holtrace_var(ty,name) ->
      hol_trace_array_add hol_trace_terms
        (mk_var(name,hol_trace_array_get hol_trace_types ty))
  | Holtrace_comb(ty,left,right) ->
      let term =
        mk_comb(hol_trace_array_get hol_trace_terms left,
                hol_trace_array_get hol_trace_terms right) in
      if type_of term <> hol_trace_array_get hol_trace_types ty
      then failwith "wrong declared type for HOLTrace combination";
      hol_trace_array_add hol_trace_terms term
  | Holtrace_abs(ty,var,body) ->
      let term =
        mk_abs(hol_trace_array_get hol_trace_terms var,
               hol_trace_array_get hol_trace_terms body) in
      if type_of term <> hol_trace_array_get hol_trace_types ty
      then failwith "wrong declared type for HOLTrace abstraction";
      hol_trace_array_add hol_trace_terms term
  | Holtrace_thm [] ->
      failwith "theorem statement has no conclusion"
  | Holtrace_thm _ ->
      if not !hol_trace_has_last then failwith "theorem without inference";
      (* This record repeats the last inference's statement, but later rules
         reference only the stored kernel theorem. Keep that theorem here;
         conform compares every requested theorem with its accepted
         statement. *)
      hol_trace_array_add hol_trace_thms !hol_trace_last
  | Holtrace_name(id,name) ->
      if not(hol_trace_identifier name) then
        failwith "invalid HOLTrace theorem name";
      if exists (fun (other,_) -> other = name) !hol_trace_names then
        failwith "repeated HOLTrace theorem name";
      hol_trace_names :=
        (name,hol_trace_array_get hol_trace_thms id):: !hol_trace_names
  | Holtrace_axiom id ->
      hol_trace_infer
        (new_axiom (hol_trace_array_get hol_trace_terms id))
  | Holtrace_beta id ->
      hol_trace_infer (BETA (hol_trace_array_get hol_trace_terms id))
  | Holtrace_refl id ->
      hol_trace_infer (REFL (hol_trace_array_get hol_trace_terms id))
  | Holtrace_assume id ->
      hol_trace_infer (ASSUME (hol_trace_array_get hol_trace_terms id))
  | Holtrace_abs_rule(term_id,thm_id) ->
      hol_trace_infer
        (ABS (hol_trace_array_get hol_trace_terms term_id)
             (hol_trace_array_get hol_trace_thms thm_id))
  | Holtrace_eq_mp(left,right) ->
      hol_trace_infer
        (EQ_MP (hol_trace_array_get hol_trace_thms left)
               (hol_trace_array_get hol_trace_thms right))
  | Holtrace_trans(left,right) ->
      hol_trace_infer
        (TRANS (hol_trace_array_get hol_trace_thms left)
               (hol_trace_array_get hol_trace_thms right))
  | Holtrace_deduct_antisym(left,right) ->
      hol_trace_infer
        (DEDUCT_ANTISYM_RULE (hol_trace_array_get hol_trace_thms left)
                             (hol_trace_array_get hol_trace_thms right))
  | Holtrace_mk_comb(left,right) ->
      hol_trace_infer
        (MK_COMB(hol_trace_array_get hol_trace_thms left,
                 hol_trace_array_get hol_trace_thms right))
  | Holtrace_inst(id,pairs) ->
      let pairs =
        map (fun (to_id,from_id) ->
            hol_trace_array_get hol_trace_terms to_id,
            hol_trace_array_get hol_trace_terms from_id) pairs in
      hol_trace_infer
        (INST pairs (hol_trace_array_get hol_trace_thms id))
  | Holtrace_inst_type(id,pairs) ->
      let pairs =
        map (fun (to_id,from_id) ->
            hol_trace_array_get hol_trace_types to_id,
            hol_trace_array_get hol_trace_types from_id) pairs in
      hol_trace_infer
        (INST_TYPE pairs (hol_trace_array_get hol_trace_thms id))
  | Holtrace_definition(id,name) ->
      let equation = hol_trace_array_get hol_trace_terms id in
      let variable,_ = dest_eq equation in
      let variable_name,_ = dest_var variable in
      if variable_name <> name then
        failwith "HOLTrace definition name differs from its variable";
      let definition = new_basic_definition equation in
      hol_trace_definitions := definition :: !hol_trace_definitions;
      hol_trace_infer definition
  | Holtrace_typedef
      (reptype_id,repprop_id,repth_id,tyname,absname,repname,tyvars) ->
      let reptype = hol_trace_array_get hol_trace_types reptype_id in
      let repprop = hol_trace_array_get hol_trace_terms repprop_id in
      let repth = hol_trace_array_get hol_trace_thms repth_id in
      let theorem_prop,witness =
        match dest_thm repth with
        | [],conclusion -> dest_comb conclusion
        | _ -> failwith "type-definition theorem has hypotheses" in
      if theorem_prop <> repprop || type_of witness <> reptype then
        failwith "bad HOLTrace type-definition witness";
      let abstraction,representation =
        new_basic_type_definition tyname (absname,repname) repth in
      let _,abstract_value = dest_eq(concl abstraction) in
      let stated_type = mk_type(tyname,map mk_vartype tyvars) in
      if type_of abstract_value <> stated_type then
        failwith "wrong type variables in HOLTrace type definition";
      hol_trace_array_add hol_trace_typedefs representation;
      hol_trace_infer abstraction
  | Holtrace_typedef_followup id ->
      hol_trace_infer (hol_trace_array_get hol_trace_typedefs id)
  | Holtrace_ignore -> ();;

let hol_trace_chomp_line line =
  let length = String.length line in
  if length = 0 ||
     Char.code line.[length - 1] <> Char.code '\n' then
    failwith "partial final HOLTrace line";
  String.sub line 0 (length - 1);;

let hol_trace_run trace =
  new_type("ind",0);
  new_constant("@",mk_fun_ty (mk_fun_ty aty bool_ty) aty);
  let stream = Text_io.openIn trace in
  let line_number = ref 0 in
  let rec loop () =
    match Text_io.inputLine stream with
    | None -> ()
    | Some raw ->
        line_number := !line_number + 1;
        let line = hol_trace_chomp_line raw in
        if !line_number = 1 then begin
          if line <> "HOLTrace 1" then
            failwith "bad HOLTrace header"
        end else begin
          (try
             let entry =
               hol_trace_decode
                 (hol_trace_array_length hol_trace_types)
                 (hol_trace_array_length hol_trace_terms)
                 (hol_trace_array_length hol_trace_thms)
                 (hol_trace_array_length hol_trace_typedefs)
                 line in
             hol_trace_replay entry
           with
           | Failure message ->
               failwith
                 ("line " ^ string_of_int !line_number ^ ": " ^ message))
        end;
        loop () in
  (try
     loop ()
   with error -> Text_io.closeIn stream; raise error);
  Text_io.closeIn stream;
  if !line_number < 1 then failwith "empty HOLTrace file";;

let hol_trace_read_names path =
  let stream = Text_io.openIn path in
  let rec loop result =
    match Text_io.inputLine stream with
    | None -> Text_io.closeIn stream; rev result
    | Some line ->
        let length = String.length line in
        let name =
          if length > 0 &&
             Char.code line.[length - 1] = Char.code '\n'
          then String.sub line 0 (length - 1)
          else line in
        if name = "" then loop result else loop (name::result) in
  loop [];;

let hol_trace_find name =
  try snd(find (fun (other,_) -> other = name) !hol_trace_names)
  with Failure _ -> failwith ("the trace does not name " ^ name);;

let hol_trace_output_char stream char =
  Text_io.output stream (String.make 1 char);;

let hol_trace_output_count stream count =
  Text_io.output stream (string_of_int count ^ ":");;

let hol_trace_output_raw stream string =
  hol_trace_output_count stream (String.length string);
  Text_io.output stream string;;

let rec hol_trace_output_type stream =
  function
  | Tyvar name ->
      hol_trace_output_char stream 'v';
      hol_trace_output_raw stream name
  | Tyapp(name,args) ->
      hol_trace_output_char stream 't';
      hol_trace_output_raw stream name;
      hol_trace_output_count stream (length args);
      do_list (hol_trace_output_type stream) args;;

let rec hol_trace_output_term stream =
  function
  | Var(name,ty) ->
      hol_trace_output_char stream 'v';
      hol_trace_output_raw stream name;
      hol_trace_output_type stream ty
  | Const(name,ty) ->
      hol_trace_output_char stream 'c';
      hol_trace_output_raw stream name;
      hol_trace_output_type stream ty
  | Comb(left,right) ->
      hol_trace_output_char stream 'a';
      hol_trace_output_term stream left;
      hol_trace_output_term stream right
  | Abs(var,body) ->
      hol_trace_output_char stream 'l';
      hol_trace_output_term stream var;
      hol_trace_output_term stream body;;

let hol_trace_output_theorem stream th =
  let hypotheses,conclusion = dest_thm th in
  hol_trace_output_char stream 'h';
  hol_trace_output_count stream (length hypotheses);
  do_list (hol_trace_output_term stream) hypotheses;
  hol_trace_output_term stream conclusion;;

let hol_trace_result_header = "HOLTRACE-RESULT-5\n";;

let hol_trace_theorem_record stream tag theorem =
  hol_trace_output_char stream tag;
  hol_trace_output_theorem stream theorem;;

let candle_holtrace trace names result =
  hol_trace_run trace;
  let requested = hol_trace_read_names names in
  let stream = Text_io.openOut result in
  Text_io.output stream hol_trace_result_header;
  do_list (hol_trace_theorem_record stream 'X') (axioms());
  do_list (hol_trace_theorem_record stream 'D') (rev !hol_trace_definitions);
  (* The typedef table holds each type definition's
     |- P r = (rep (abs r) = r), which conform reads. *)
  let rec typedefs index =
    if index < hol_trace_array_length hol_trace_typedefs then begin
      hol_trace_theorem_record stream 'Y'
        (hol_trace_array_get hol_trace_typedefs index);
      typedefs (index + 1)
    end else () in
  typedefs 0;
  do_list (fun name ->
      hol_trace_output_char stream 'T';
      hol_trace_output_raw stream name;
      hol_trace_output_theorem stream (hol_trace_find name))
    requested;
  hol_trace_output_char stream 'S';
  Text_io.closeOut stream;;

let candle_holtrace_failure result message =
  let stream = Text_io.openOut result in
  Text_io.output stream hol_trace_result_header;
  hol_trace_output_char stream 'F';
  hol_trace_output_raw stream message;
  Text_io.closeOut stream;;
