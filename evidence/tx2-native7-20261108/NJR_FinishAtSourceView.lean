import NJR_ViewFinish
set_option autoImplicit false
noncomputable section
namespace NJR_FinishAtSourceView
open Aeneas Aeneas.Std Result AspisR1 AspisR1Stage2 NIT_Cuts
/-- The CLOSED finish law at the literal frozen caller View. The raw slice
clauses are proved here, and Domain is derived inside the call installation.
This remains internal source work until actual scan/history is attached. -/
theorem at_source_view (reserved : Bool) (r : NP6_StdModel.Reservation)
 (loc : NIW_AlignFinishComposed.Locations) {H : Type} (d : aspis_core.digest.Digest32 H)
 (ck proof pub : Slice U8) (hash : H) (p : verifier.Prepared) (a after : verifier.Accumulator)
 (g : Array aspis_core.field.wide_exact.WideExact 29#usize)
 (geometry : verifier.QueryGeometry) (pending : verifier.BatchedWeights) (inactive : aspis_core.field.wide_exact.WideExact)
 (ckSize : ck.val.length=1768)
 (resume : verifier.resumeWithOps (CheckpointBytes4Ops.ops reserved) d ck proof pub .S2 hash=ok (.Ok (p,a)))
 (start : a.next.val=10)
 (query : Port3_NativeQueryBody.verifier.candidate.query_loop
  (NFS_QueryOps.installed NJJ_QueryOps.concrete) proof p a g none geometry
  (NFW_QueryResume.pending a) 22#usize=ok (.Ok (after,pending)))
 (proofLength : proof.val.length=57607)
 (scan : Op4P_Install.sourceBody proof=ok (.Ok ())) :
 ∃ out : Slice aspis_core.field.QM31,
 Port3_FlushInstall.flush pending after.weights.deref=ok out ∧
 let actual : verifier.Accumulator := {after with weights:=⟨out.val,out.property⟩}
 ∀ (port : PairPort) (afterOwner : Nat),
 NIW_AlignFinishPort.Cut p port afterOwner (NJF_FinishObserved.G r loc (NJR_ViewFinish.view proof inactive) p actual).2.2 →
 let execution:=NJF_FinishObserved.G r loc (NJR_ViewFinish.view proof inactive) p actual
 Port3_NativeFinishBody.verifier.finish_relation (NIG_Slots.installed r) (NJR_ViewFinish.view proof inactive) p actual none=execution.1 ∧
 (∀ event∈execution.2.1,NIW_AlignFinishInvocation.Clause r event) ∧
 (∀ event∈execution.2.1,NIW_AlignFinishDomains.Inputs p (NJR_ViewFinish.view proof inactive) actual event) ∧
 NIW_AlignFinishPrefix.Prefix execution.2.1 ∧
 NIW_AlignFinishPairCertificate.Bound r execution.2.2 ∧
 NIW_AlignFinishInfoEvent.HasPair execution ∧ NIW_AlignFinishInfoNew.HasNew p execution ∧
 NIW_AlignFinishPort.Bound r port execution.2.2 := by
 exact NJR_FinishInstall.at_call reserved r loc d ck proof pub hash p a after g geometry pending
  (NJR_ViewFinish.view proof inactive) ckSize resume start query proofLength rfl rfl rfl scan

#print at_source_view
#print axioms at_source_view
end NJR_FinishAtSourceView
