import NLP_FoldedRange
import NKO_C03Core
set_option autoImplicit false
noncomputable section
namespace NLP_C04Folded
open Aeneas Aeneas.Std Result VTop_Stages AspisR1 NJU_CommonObserved
/-- Literal checked range/array-copy/unwrap chain at C04. -/
def Holds (proof : Slice U8) : Event → Prop
 | .merkle pr _ folded _ => pr=proof ∧ ∃ (s : Slice U8)
   (r : core.result.Result (Array U8 32#usize) core.array.TryFromSliceError),
   core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
    proof {start:=7751#usize,«end»:=7783#usize}=ok s ∧
   core.array.TryFromArrayCopySlice.try_from 32#usize core.marker.CopyU8 s=ok r ∧
   core.result.Result.unwrap core.fmt.DebugTryFromSliceError r=ok folded
 | _ => True
end NLP_C04Folded
open Lean Elab Tactic
elab "nlp_folded_record" : tactic => do
 let t ← getMainTarget
 unless t.isAppOf ``NKE_EventAll.Holds do throwError "not event property"
 unless t.getAppArgs.back!.isAppOf ``NJU_Log.record do throwError "not record"
 evalTactic (← `(tactic| apply NKE_EventAll.record_all))
 let t ← getMainTarget
 if t.getAppArgs.back!.getAppFn.constName?.getD Name.anonymous == `NJU_CommonObserved.Event.merkle then
  evalTactic (← `(tactic|
   simp_all only [NJU_Log.erase_lift,NJU_Log.erase_liftM,Result.ok.injEq]
   refine ⟨rfl,_,_,?_,?_,?_⟩ <;> assumption))
 else evalTactic (← `(tactic| exact True.intro))
namespace NLP_C04Folded
open Aeneas Aeneas.Std Result VTop_Stages AspisR1 NJU_CommonObserved
theorem source (wr rr : NP6_StdModel.Reservation) (merkle : Merkle) (finish : Finish)
 {H : Type} (d : aspis_core.digest.Digest32 H) (pub proof ck : Slice U8) (hash : H) :
 NKE_EventAll.Holds (Holds proof) (run wr rr merkle finish d pub proof ck hash none) := by
 unfold NJU_CommonObserved.run
 simp only [NKO_Offsets.folded,NKO_Offsets.round1]
 repeat' first
 | nke_zeta
 | nko_c03_bind
 | nke_intro
 | nke_lift
 | nke_pure
 | nlp_folded_record
 | (fail_if_no_progress dsimp only [NJU_Log.prod_cases])
 | split
/-- Every reached folded root uses the original current proof bytes. -/
theorem at_actual (wr rr : NP6_StdModel.Reservation) (merkle : Merkle) (finish : Finish)
 {H : Type} (d : aspis_core.digest.Digest32 H) (pub proof ck : Slice U8) (hash : H)
 (pr : Slice U8) (p : verifier.Prepared) (folded : Array U8 32#usize) (reply : R Unit)
 (entered : Event.merkle pr p folded reply∈(run wr rr merkle finish d pub proof ck hash none).events) :
 pr=proof ∧ folded.val=(proof.val.drop 7751).take 32 := by
 obtain ⟨same,s,r,range,copy,unwrap⟩:=source wr rr merkle finish d pub proof ck hash _ entered
 cases r with
 | Err e => cases unwrap
 | Ok root =>
   have eq:=Result.ok.inj unwrap
   subst root
   exact ⟨same,(NLP_FoldedRange.copied s folded copy).trans (NLP_FoldedRange.selected proof s range)⟩
set_option pp.proofs false
#print source
#print at_actual
#print axioms source
#print axioms at_actual
end NLP_C04Folded
