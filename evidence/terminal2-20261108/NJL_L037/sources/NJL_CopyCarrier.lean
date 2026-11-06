import NIH_SelectedBinary
open Lean Elab Command
#print Aeneas.Std.core.marker.Copy
run_cmd do
 let env ← getEnv
 for (name, info) in env.constants.toList do
  let text := name.toString
  if text.startsWith "FIq_Native.field" && text.contains "Copy" then
   logInfo m!"{name}: {info.type}"
