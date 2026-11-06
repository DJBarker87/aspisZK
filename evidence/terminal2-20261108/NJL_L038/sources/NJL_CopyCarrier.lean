import NIH_SelectedBinary
open Lean Elab Command
#print Aeneas.Std.core.marker.Copy
run_cmd do
 let env ← getEnv
 for entry in env.constants.toList do
  let name := entry.1
  let declaration := entry.2
  let text := name.toString
  if text.startsWith "FIq_Native.field"  then
   logInfo m!"{name}: {declaration.type}"
