import NKE_ViewCut
import NJU_FinishAtCurrent
set_option autoImplicit false
noncomputable section
namespace NKE_FinishSupplement
open Aeneas Aeneas.Std Result AspisR1 AspisR1Stage2 NIT_Cuts NIW_AlignFinishComposed
/-- Unchanged (aw) child supplement, retaining all SAME-call facts/cuts.
This re-export is not a new positive tx2_common root or a row promotion. -/
theorem finish (r : NP6_StdModel.Reservation) (loc : Locations) (proof : Slice U8)
 (v : verifier.View) (p : verifier.Prepared) (a : verifier.Accumulator)
 (facts : NJU_FinishInput.Holds proof v p a) :
 let execution:=NJF_FinishObserved.G r loc v p a
 Port3_NativeFinishBody.verifier.finish_relation (NIG_Slots.installed r) v p a none=execution.1 ∧
 NIW_AlignFinishComposedLog.forget execution=NIW_AlignFinishExecution.run r v p a ∧
 NIW_AlignFinishPrefix.Prefix execution.2.1 := by
 exact AspisR1.NJU_GeneralFinishRoot.finish r loc proof v p a facts
#print finish
#print axioms finish
theorem ported (r : NP6_StdModel.Reservation) (loc : Locations) (proof : Slice U8)
 (v : verifier.View) (p : verifier.Prepared) (a : verifier.Accumulator)
 (facts : NJU_FinishInput.Holds proof v p a) (port : PairPort) (afterOwner : Nat)
 (cut : NIW_AlignFinishPort.Cut p port afterOwner (NJF_FinishObserved.G r loc v p a).2.2) :
 let execution:=NJF_FinishObserved.G r loc v p a
 Port3_NativeFinishBody.verifier.finish_relation (NIG_Slots.installed r) v p a none=execution.1 ∧
 NIW_AlignFinishComposedLog.forget execution=NIW_AlignFinishExecution.run r v p a ∧
 NIW_AlignFinishPrefix.Prefix execution.2.1 ∧
 NJU_WeakFinishPairCertificate.Bound r execution.2.2 ∧
 NIW_AlignFinishPort.Bound r port execution.2.2 := by
 exact AspisR1.NJU_GeneralFinishRoot.ported r loc proof v p a facts port afterOwner cut
#print ported
#print axioms ported
theorem at_current (reserved : Bool) (r : NP6_StdModel.Reservation)
 (loc : NIW_AlignFinishComposed.Locations) {H : Type} (d : aspis_core.digest.Digest32 H)
 (ck proof pub : Slice U8) (hash : H) (p : verifier.Prepared) (a after : verifier.Accumulator)
 (g : Array aspis_core.field.wide_exact.WideExact 29#usize)
 (geometry : verifier.QueryGeometry) (pending : verifier.BatchedWeights)
 (inactive : aspis_core.field.wide_exact.WideExact)
 (ckSize : ck.val.length=1768)
 (resume : verifier.resumeWithOps (CheckpointBytes4Ops.ops reserved) d ck proof pub .S2 hash=ok (.Ok (p,a)))
 (start : a.next.val=10)
 (query : Port3_NativeQueryBody.verifier.candidate.query_loop
  (NFS_QueryOps.installed NJJ_QueryOps.concrete) proof p a g none geometry
  (NFW_QueryResume.pending a) 22#usize=ok (.Ok (after,pending)))
 (size : 10055≤proof.val.length) :
 ∃ out : Slice aspis_core.field.QM31,
 Port3_FlushInstall.flush pending after.weights.deref=ok out ∧
 let v:=NJR_ViewFinish.view proof inactive
 let actual : verifier.Accumulator := {after with weights:=⟨out.val,out.property⟩}
 ∀ (port : PairPort) (afterOwner : Nat),
 NIW_AlignFinishPort.Cut p port afterOwner (NJF_FinishObserved.G r loc v p actual).2.2 →
 let execution:=NJF_FinishObserved.G r loc v p actual
 Port3_NativeFinishBody.verifier.finish_relation (NIG_Slots.installed r) v p actual none=execution.1 ∧
 NIW_AlignFinishComposedLog.forget execution=NIW_AlignFinishExecution.run r v p actual ∧
 NIW_AlignFinishPrefix.Prefix execution.2.1 ∧
 NJU_WeakFinishPairCertificate.Bound r execution.2.2 ∧
 NIW_AlignFinishPort.Bound r port execution.2.2 := by
 exact NJU_FinishAtCurrent.source_view reserved r loc d ck proof pub hash p a after g geometry pending inactive ckSize resume start query size
#print at_current
#print axioms at_current
end NKE_FinishSupplement
