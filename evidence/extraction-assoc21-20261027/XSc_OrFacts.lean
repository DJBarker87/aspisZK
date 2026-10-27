import XSc_RecordFieldTypes
open Lean Elab Command in
run_cmd do
 let env ← getEnv
 for (n,_) in env.constants.toList do
  let s := n.toString
  if s.startsWith "Nat." then
   if (s.splitOn "or").length>1 then
    if (s.splitOn "add").length>1 ∨ (s.splitOn "shift").length>1 ∨ (s.splitOn "two_pow").length>1 then
     logInfo m!"{n}"
