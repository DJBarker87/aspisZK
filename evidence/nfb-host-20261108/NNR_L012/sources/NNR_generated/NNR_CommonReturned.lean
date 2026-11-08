import NNR_ReturnedLog
import Lean
open Lean Elab Tactic
private def nnrRun : TacticM Expr := do
 let t ← getMainTarget
 unless t.isAppOf ``AspisR1.NNR_ReturnedLog.Safe do throwError "not Safe"
 return t.getAppArgs.back!
elab "nnr_bind" : tactic => do
 let m ← nnrRun
 unless m.isAppOf ``Bind.bind do throwError "not bind"
 evalTactic (← `(tactic| apply AspisR1.NNR_ReturnedLog.bind_safe))
elab "nnr_lift" : tactic => do
 let m ← nnrRun
 unless m.isAppOf ``MonadLiftT.monadLift || m.isAppOf ``liftM do throwError "not lift"
 evalTactic (← `(tactic| exact AspisR1.NNR_ReturnedLog.lift_safe _))
elab "nnr_pure" : tactic => do
 let m ← nnrRun
 unless m.isAppOf ``Pure.pure do throwError "not pure"
 evalTactic (← `(tactic| exact AspisR1.NNR_ReturnedLog.pure_safe _))
elab "nnr_record" : tactic => do
 let m ← nnrRun
 unless m.isAppOf ``NJU_Log.record do throwError "not record"
 evalTactic (← `(tactic| apply AspisR1.NNR_ReturnedLog.record_safe))
 evalTactic (← `(tactic| intro value))
 evalTactic (← `(tactic| first | exact True.intro | exact ⟨value,rfl⟩))
elab "nnr_zeta" : tactic => do
 let m ← nnrRun
 let .letE _ _ value body _ := m | throwError "not let"
 liftMetaTactic fun goal => do
  let target ← goal.getType
  let args := target.getAppArgs
  return [← goal.change (mkAppN target.getAppFn (args.pop.push (body.instantiate1 value)))]
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNR_CommonReturned
open Aeneas Aeneas.Std Result VTop_Stages NJU_CommonObserved NNR_ReturnedLog
/-- Only visible log combinators are traversed; child definitions stay opaque. -/
theorem safe (wr rr : NP6_StdModel.Reservation) (merkle : Merkle) (finish : Finish)
 {X : Type} (d : aspis_core.digest.Digest32 X) (pub proof ck : Slice U8) (hash : X) :
 Safe (NJU_CommonObserved.run wr rr merkle finish d pub proof ck hash none) := by
 unfold NJU_CommonObserved.run
 repeat' first
 | nnr_zeta
 | nnr_bind
 | nke_intro
 | nnr_lift
 | nnr_pure
 | nnr_record
 | (fail_if_no_progress dsimp only [NJU_Log.prod_cases])
 | split
#print axioms safe
end AspisR1.NNR_CommonReturned
end
