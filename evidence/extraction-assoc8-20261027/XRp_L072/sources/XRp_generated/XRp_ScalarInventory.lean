import XRo_Join_Installed
open Lean
run_cmd do
  let env ← getEnv
  for (n,_) in env.constants.toList do
    if ("Aeneas.Std.UScalar".isPrefixOf n.toString || "Aeneas.Std.U32".isPrefixOf n.toString) &&
      ((n.toString.splitOn "wrapp").length > 1 || (n.toString.splitOn "equiv").length > 1) then
      logInfo m!"{n}"
