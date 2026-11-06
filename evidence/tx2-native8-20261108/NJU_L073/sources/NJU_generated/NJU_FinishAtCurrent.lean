import NJU_GeneralFinishRoot
import NJU_FinishCaller
import NJR_ViewFinish
set_option autoImplicit false
noncomputable section
namespace NJU_FinishAtCurrent
open Aeneas Aeneas.Std Result AspisR1 AspisR1Stage2 NIT_Cuts

/-- Install the generalized finish bridge at the literal CURRENT View after
SAME resume/query/flush. No raw-word, history, NoBad, proof persistence or
finish-success premise. Internal bind inversions are not new root inputs. -/
theorem source_view (reserved : Bool) (r : NP6_StdModel.Reservation)
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
 obtain ⟨out,flush,facts⟩:=NJU_FinishCaller.reached reserved d ck proof pub hash p a after g geometry
  pending (NJR_ViewFinish.view proof inactive) ckSize resume start query size rfl rfl rfl
 refine ⟨out,flush,?_⟩
 dsimp only
 intro port afterOwner cut
 exact NJU_GeneralFinishRoot.ported r loc proof _ p _ facts port afterOwner cut

#print source_view
#print axioms source_view
end NJU_FinishAtCurrent
