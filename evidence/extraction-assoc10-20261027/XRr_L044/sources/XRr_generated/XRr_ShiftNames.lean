import XRn_Join_Funs
open Lean
run_cmd do
 let env ← getEnv
 for (name,_) in env.constants.toList do
  if name.toString.startsWith "Aeneas.Std.UScalar" &&
     (name.toString.splitOn "shiftRight").length > 1 then
   logInfo m!"{name}"
