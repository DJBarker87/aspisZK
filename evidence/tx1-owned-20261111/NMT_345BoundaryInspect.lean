import NMT_345RawSelected
import NMT_345Raw_00
import NMT_345Distinct
import Lean
open Lean Elab Command
run_cmd do
 let env ← getEnv
 for decl in [Name.str (Name.str Name.anonymous "NMT_345") "rawSelected", Name.str (Name.str Name.anonymous "NMT_345") "raw00", Name.str (Name.str Name.anonymous "NMT_345") "emitted_try"] do
  let some info := env.find? decl | throwError "missing {decl}"
  let some value := info.value? | throwError "no value {decl}"
  for n in value.getUsedConstants do
   if (n.toString.splitOn "FromSame").length > 1 then
    logInfo m!"{decl} uses {n}"
set_option pp.fullNames true in
#print NMT_345.emitted_try
