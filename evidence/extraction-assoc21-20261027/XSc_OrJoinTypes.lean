import XSc_RecordFieldTypes
#print Nat.shiftLeft_add_eq_or_of_lt
open Lean Elab Command in
run_cmd do
 let env ← getEnv
 for (n,c) in env.constants.toList do
  let s := n.toString
  if s.startsWith "Nat." then
   if (s.splitOn "shiftLeft_eq").length>1 then
    logInfo m!"{n}: {c.type}"
