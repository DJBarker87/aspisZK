import NEW_GeometryActual.Funs
import NEB_GeometryDictionaryEq
run_cmd do
 let env ← Lean.getEnv
 for entry in env.constants.toList do
  let text := entry.1.toString
  if text.startsWith "Aeneas.Std" && ((text.splitOn "shr").length>1 || (text.splitOn "ShiftRight").length>1 || (text.splitOn "loop").length>1) then
   Lean.logInfo m!"{entry.1}"
