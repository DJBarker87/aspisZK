import R1Z.PV_CB3_StagedPacking
open Lean Elab Command
#print bne
run_cmd do
  for (n,_) in (← getEnv).constants.toList do
    if (`Aeneas.Std.UScalar).isPrefixOf n then logInfo m!"{n}"
