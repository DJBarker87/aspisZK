import Aeneas.Std
#print Aeneas.Std.core.fmt.Formatter
#print axioms Aeneas.Std.core.fmt.Formatter
open Lean Elab Command
run_cmd do
 let environment ← getEnv
 for (name, info) in environment.constants.toList do
  if name.toString.startsWith "Aeneas.Std.core.fmt" then
   logInfo m!"{name} : {info.type}"
