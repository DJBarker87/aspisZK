import XRn_Join_Funs
open Lean
run_cmd do
  let env ← getEnv
  for (n,_) in env.constants.toList do
    if "Aeneas.Std.loop".isPrefixOf n.toString || "Lean.Order.fix".isPrefixOf n.toString then
      logInfo m!"{n}"
