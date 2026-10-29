import PV_B3P_ClosureLinks14227
open Lean Elab Command
run_cmd do
 let environment ← getEnv
 for (name, info) in environment.constants.toList do
  if ["Aeneas.Std.core.clone", "Aeneas.Std.core.cmp", "Aeneas.Std.core.option", "Aeneas.Std.core.slice"].any (fun start => name.toString.startsWith start) then
   logInfo m!"{name} : {info.type}"
