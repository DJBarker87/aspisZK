import NIT_LowInterpretation
open Lean Elab Command
run_cmd do
 for (name, _) in (← getEnv).constants do
  let s := name.toString
  if s.startsWith "Aeneas.Std.UScalar." &&
    ((s.splitOn "shr").length>1 || (s.splitOn "ofNat").length>1 || (s.splitOn "val_and").length>1) then
   logInfo m!"{name}"
