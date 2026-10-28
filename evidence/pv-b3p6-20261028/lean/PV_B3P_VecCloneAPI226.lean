import Aeneas.Std
open Aeneas Aeneas.Std Lean Elab Command
#print core.clone.Clone
#print Slice.clone
#print alloc.vec.Vec.length
#print Slice.length
run_cmd do
  let env ← getEnv
  for (name, _) in env.constants.toList do
    if (name.toString.splitOn "U8").length > 1 &&
       ((name.toString.splitOn "Clone").length > 1 ||
        (name.toString.splitOn "clone").length > 1) then
      logInfo m!"{name}"
