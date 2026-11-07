import NNH_ValidateFission
open Lean in
run_cmd do
 let env ← getEnv
 for (n,_) in env.constants.toList do
  let s := n.toString
  if s.startsWith "Aeneas.Std.UScalar" && ((s.splitOn "mul").length>1 || (s.splitOn "add").length>1 || (s.splitOn "tryMk").length>1) then
   logInfo m!"{n}"
