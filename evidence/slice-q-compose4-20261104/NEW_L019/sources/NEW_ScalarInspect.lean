import NEW_GeometryActual.Funs
import NEB_GeometryDictionaryEq
run_cmd do
 let env ← Lean.getEnv
 for (name,_) in env.constants.toList do
  let n := name.toString
  if n.startsWith "Aeneas.Std.UScalar" && ((n.splitOn "shr").length>1 || (n.splitOn "Shift").length>1) then
   Lean.logInfo m!"{name}"
