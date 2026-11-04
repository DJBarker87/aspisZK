import NEW_GeometryActual.Funs
import NEB_GeometryDictionaryEq
#print Lean.Order.admissible
#print Aeneas.Std.UScalar.shiftRight_IScalar
run_cmd do
 let env ← Lean.getEnv
 for entry in env.constants.toList do
  let text := entry.1.toString
  if text.startsWith "System.Platform" || text.startsWith "Lean.Order.admissible" || text.startsWith "Aeneas.Std.Result.inst" then
   Lean.logInfo m!"{entry.1}"
