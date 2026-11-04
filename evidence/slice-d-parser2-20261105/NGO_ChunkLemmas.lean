import NGD_DecodeEntry
open Aeneas Aeneas.Std Result
run_cmd do
 for (n,ci) in (← Lean.getEnv).constants.toList do
  if n.toString.contains "toChunksExact" && !n.toString.contains "_proof" then
   Lean.logInfo m!"{n}: {ci.type}"
