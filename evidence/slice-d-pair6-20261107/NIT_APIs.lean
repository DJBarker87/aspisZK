import NIT_LowInterpretation
open Lean Elab Command
run_cmd do
 let env ← getEnv
 for entry in env.constants.toList do
  let s := entry.1.toString
  if s.startsWith "Aeneas.Std.UScalar." &&
    ((s.splitOn "shr").length>1 || (s.splitOn "ofNat").length>1 || (s.splitOn "val_and").length>1) then
   logInfo m!"{entry.1}"
