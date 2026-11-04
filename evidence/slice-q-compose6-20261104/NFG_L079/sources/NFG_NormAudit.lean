import Mathlib.NumberTheory.LegendreSymbol.Basic
open Lean Elab Command in
run_cmd do
 let env ← getEnv
 for (name, _) in env.constants.toList do
  let s := name.toString
  if s.startsWith "ZMod." && (s.isInfixOf "dummy" || "neg_one".isInfixOf s || "sq_add_sq".isInfixOf s) then
   logInfo m!"{name}"
