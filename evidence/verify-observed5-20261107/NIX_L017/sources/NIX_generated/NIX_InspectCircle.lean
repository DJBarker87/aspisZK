import NIH_COMBINED_IMPORT
import NGX_RecordAt
open Aeneas Aeneas.Std Result
#print AspisR1.NGX_RecordAt.computation
open Lean Elab Command
run_cmd do
 let env ← getEnv
 for (n,_) in env.constants.toList do
  if ["secure_circle_point_from_parameter","secure_ood_circle_point_from_parameter","circle_fallback_point","secure_circle_eq_r72"].any (fun s=>n.toString.endsWith s) then logInfo m!"NIX_DECL {n}"
