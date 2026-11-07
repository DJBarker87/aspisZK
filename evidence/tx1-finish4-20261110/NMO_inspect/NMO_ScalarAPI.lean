import NMO_PrefixBounds
open Lean Elab Command
run_cmd do
 let env ← getEnv
 for (name, info) in env.constants.toList do
  if name.toString.startsWith "Aeneas.Std.UScalar.add" || name.toString.startsWith "Aeneas.Std.UScalar.tryMk" then
   logInfo m!"{name} : {info.type}"
#print Aeneas.Std.UScalar.add
