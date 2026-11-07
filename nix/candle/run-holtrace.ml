(*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 *)

loads "candle/pft/pft.ml";;

let candle_holtrace_args = tl(Cake.Command_line.arguments ());;
if length candle_holtrace_args <> 3 then begin
  print_endline "usage: candle-holtrace TRACE NAMES RESULT";
  Cake.Runtime.exit 2
end else ();;
let candle_holtrace_trace = hd candle_holtrace_args;;
let candle_holtrace_names = hd(tl candle_holtrace_args);;
let candle_holtrace_result = hd(tl(tl candle_holtrace_args));;

loads "candle/holtrace_restore.ml";;

try
  candle_holtrace
    candle_holtrace_trace candle_holtrace_names candle_holtrace_result;
  Cake.Runtime.exit 0
with error ->
  let message =
    match error with
    | Failure message -> message
    | Sys_error message -> message
    | Invalid_argument message -> message
    | _ -> "Candle HOLTrace replay failed" in
  print_endline ("candle-holtrace: " ^ message);
  candle_holtrace_failure candle_holtrace_result message;
  Cake.Runtime.exit 1;;
