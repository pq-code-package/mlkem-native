/- Copyright (c) The mlkem-native project authors
   SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT -/

import HolTrace.Restore

open HolCore.Kernel

/- HolLean's HolTrace.verifyFile performs the replay, starting from a bare
   kernel.  This adapter writes the replayed theory in the result format
   described in proofs/hol_light/hol_trace/term_encoding.ml; `hol-trace
   compare` applies the acceptance policy. -/
namespace HolTraceAdapter

private def addChar (out : ByteArray) (char : Char) : ByteArray :=
  out.push char.toNat.toUInt8

private def addBytes (out bytes : ByteArray) : ByteArray := Id.run do
  let mut result := out
  for byte in bytes do
    result := result.push byte
  return result

private def addString (out : ByteArray) (text : String) : ByteArray :=
  addBytes out text.toUTF8

private def addRaw (out : ByteArray) (text : String) : ByteArray :=
  addString (addChar (addString out (toString text.toUTF8.size)) ':') text

private def addCount (out : ByteArray) (count : Nat) : ByteArray :=
  addChar (addString out (toString count)) ':'

private def addType : ByteArray → hol_type → ByteArray
  | out, .Tyvar name =>
      addRaw (addChar out 'v') name
  | out, .Tyapp name args =>
      args.foldl addType (addCount (addRaw (addChar out 't') name) args.length)

private def addTerm : ByteArray → term → ByteArray
  | out, .Var name ty =>
      addType (addRaw (addChar out 'v') name) ty
  | out, .Const name ty =>
      addType (addRaw (addChar out 'c') name) ty
  | out, .Comb lhs rhs =>
      addTerm (addTerm (addChar out 'a') lhs) rhs
  | out, .Abs var body =>
      addTerm (addTerm (addChar out 'l') var) body

private def addTheorem (out : ByteArray) (th : thm) : ByteArray :=
  let (hyps, concl) := dest_thm th
  addTerm (hyps.foldl addTerm (addCount (addChar out 'h') hyps.length)) concl

private def header : ByteArray := "HOLTRACE-RESULT-5\n".toUTF8

private def requiredEnv (name : String) : IO String := do
  match ← IO.getEnv name with
  | some value => return value
  | none => throw (IO.userError s!"{name} is not set")

private def namesFrom (path : String) : IO (List String) := do
  let contents ← IO.FS.readFile path
  return contents.splitOn "\n" |>.filter (!·.isEmpty)

def failureResult (message : String) : ByteArray :=
  addRaw (addChar header 'F') message

def check : IO (String × ByteArray) := do
  let trace ← requiredEnv "HOLTRACE_TRACE"
  let namesPath ← requiredEnv "HOLTRACE_NAMES"
  let resultPath ← requiredEnv "HOLTRACE_RESULT"
  let names ← namesFrom namesPath
  let state ←
    match ← (HolTrace.verifyFile {} trace).run with
    | .ok state => pure state
    | .error message => throw (IO.userError message)
  let mut result := header
  for th in ← axioms do
    result := addTheorem (addChar result 'X') th
  for th in ← definitions do
    result := addTheorem (addChar result 'D') th
  -- The typedef table holds each type definition's
  -- |- P r = (rep (abs r) = r), which conform reads.
  for th in state.typedefs do
    result := addTheorem (addChar result 'Y') th
  for name in names do
    let some th := state.find? name
      | throw (IO.userError s!"the trace does not name {name}")
    result := addTheorem (addRaw (addChar result 'T') name) th
  return (resultPath, addChar result 'S')

end HolTraceAdapter

def main : IO UInt32 := do
  let resultPath? ← IO.getEnv "HOLTRACE_RESULT"
  try
    let (resultPath, result) ← HolTraceAdapter.check
    IO.FS.writeBinFile resultPath result
    return 0
  catch error =>
    let message := toString error
    IO.eprintln s!"hollean-holtrace: {message}"
    match resultPath? with
    | some resultPath =>
        IO.FS.writeBinFile resultPath (HolTraceAdapter.failureResult message)
    | none => pure ()
    return 1
