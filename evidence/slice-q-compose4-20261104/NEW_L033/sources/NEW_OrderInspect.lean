import NEW_GeometryActual.Funs
import NEB_GeometryDictionaryEq
#check @Lean.Order.admissible_flatOrder
#check @Lean.Order.admissible_pi_apply
#check @Lean.Order.admissible_pi
#print Lean.Order.CCPO
run_cmd do
 let env ← Lean.getEnv
 for entry in env.constants.toList do
  let text := entry.1.toString
  if text.startsWith "Aeneas.Std" && ((text.splitOn "Result").length>1) && ((text.splitOn "inst").length>1) then
   Lean.logInfo m!"{entry.1}"
