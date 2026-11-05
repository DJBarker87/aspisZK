import Lean
import NHC_NGG_SpineRef.Funs

set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NHC_NGG_DecodePrefix
open NHC_NGG_SpineRef
def finish {R : Type} (decoded : core.result.Result R NGGSpineError)
    (count : Usize) (hints : Hints) :
    core.result.Result (R × Array Usize 3#usize × Hints) NGGSpineError :=
  match decoded with
  | .Err e => .Err e
  | .Ok r => if count = 0#usize then .Err .NotEnoughAccountKeys
    else if count < 2#usize then .Err .NotEnoughAccountKeys
    else if count < 3#usize then .Err .NotEnoughAccountKeys
    else .Ok (r,Array.make 3#usize [0#usize,1#usize,2#usize],hints)

def resume {R : Type} (decoded : core.result.Result R NGGSpineError)
    (count : Usize) (hints : Hints) : Result (core.result.Result (R × Array Usize 3#usize × Hints) NGGSpineError) := do
  let cf ← core.result.Result.Insts.CoreOpsTry.branch decoded
  match cf with
  | .Continue r =>
    if count = 0#usize then ok (.Err .NotEnoughAccountKeys)
    else if count < 2#usize then ok (.Err .NotEnoughAccountKeys)
    else if count < 3#usize then ok (.Err .NotEnoughAccountKeys)
    else ok (.Ok (r,Array.make 3#usize [0#usize,1#usize,2#usize],hints))
  | .Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      (R × Array Usize 3#usize × Hints) (core.convert.FromSame NGGSpineError) residual

theorem resume_eq {R : Type} (decoded : core.result.Result R NGGSpineError)
    (count : Usize) (hints : Hints) : resume decoded count hints = ok (finish decoded count hints) := by
  cases decoded with
  | Err e => rfl
  | Ok r =>
    simp only [resume,finish,core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
    split_ifs <;> rfl
#print axioms resume_eq
end NHC_NGG_DecodePrefix

run_cmd do
 let env ← Lean.getEnv
 env.constants.toList.forM fun (n, ci) => do
  if ci.isTheorem && (env.getModuleIdxFor? n).isNone then
   Lean.Elab.Command.elabCommand (← `(command| #print axioms $(Lean.mkIdent n)))
