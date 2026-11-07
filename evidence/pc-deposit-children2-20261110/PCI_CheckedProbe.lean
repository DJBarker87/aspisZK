import Aeneas
open Lean Elab Command
run_cmd do
 let env ← Lean.getEnv
 for (n,ci) in env.constants.toList do
  let s := n.toString
  if (s.splitOn "checked_add").length>1 then
   logInfo m!"DEF {s}\nTYPE {ci.type}\nVALUE {ci.value? true}"
