import Aeneas
open Lean Elab Command
run_cmd do
 let env ← Lean.getEnv
 for (n,ci) in env.constants.toList do
  let s := n.toString
  if (s.splitOn "toLEBytes").length > 1 then
   logInfo m!"FOUND {s}\nTYPE {ci.type}"
   if s.endsWith ".toLEBytes" then logInfo m!"VALUE {ci.value? true}"
