import R1Z.PV_CBL_PathJoinChecked
import R1Z.PV_CBL_VectorPopSpec
import R1Z.PV_CBL_ArrayResult
open Lean Elab Command
run_cmd do
  let env ← getEnv
  for (n,c) in env.constants.toList do
    let s := n.toString
    if s.startsWith "Aeneas.Std.alloc.vec.Vec" || s.startsWith "Aeneas.Std.String" then
      logInfo m!"{n} : {c.type}"
#print String
#print Aeneas.Std.Str
