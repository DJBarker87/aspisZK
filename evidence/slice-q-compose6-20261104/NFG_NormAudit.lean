import Mathlib.NumberTheory.LegendreSymbol.Basic
open Lean Elab Command in
run_cmd do
 let env ← getEnv
 for (name, _) in env.constants.toList do
  let s := name.toString
  if s.startsWith "ZMod." && (s.endsWith "neg_one" || s.endsWith "neg_one_iff" || s.endsWith "sq_eq_neg_one_iff" || s.endsWith "sq_add_sq_eq_zero_iff") then
   logInfo m!"{name}"
