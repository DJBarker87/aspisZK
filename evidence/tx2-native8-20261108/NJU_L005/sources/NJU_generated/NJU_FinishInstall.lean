import NJU_FinishDomain
import NJF_Root
set_option autoImplicit false
noncomputable section
namespace NJU_FinishInstall
open Aeneas Aeneas.Std Result AspisR1 AspisR1Stage2 NIT_Cuts

/-- Install CLOSED finish on the good CURRENT-byte branch. Domain is derived
from SAME resume/query/flush and current windows. No history, NoBad, persistence
or finish-success premise. This internal branch is not TX2:065. -/
theorem at_call (reserved : Bool) (r : NP6_StdModel.Reservation)
 (loc : NIW_AlignFinishComposed.Locations) {H : Type} (d : aspis_core.digest.Digest32 H)
 (ck proof pub : Slice U8) (hash : H) (p : verifier.Prepared) (a after : verifier.Accumulator)
 (g : Array aspis_core.field.wide_exact.WideExact 29#usize)
 (geometry : verifier.QueryGeometry) (pending : verifier.BatchedWeights) (v : verifier.View)
 (ckSize : ck.val.length=1768)
 (resume : verifier.resumeWithOps (CheckpointBytes4Ops.ops reserved) d ck proof pub .S2 hash=ok (.Ok (p,a)))
 (start : a.next.val=10)
 (query : Port3_NativeQueryBody.verifier.candidate.query_loop
  (NFS_QueryOps.installed NJJ_QueryOps.concrete) proof p a g none geometry
  (NFW_QueryResume.pending a) 22#usize=ok (.Ok (after,pending)))
 (proofLength : proof.val.length=57607)
 (round0 : v.round0.val=(proof.val.drop 7527).take 224)
 (round1 : v.round1.val=(proof.val.drop 7783).take 224)
 (finalView : v.final_message.val=(proof.val.drop 8007).take 2048)
 (windows : NJU_CurrentWindows.Holds v) :
 ∃ out : Slice aspis_core.field.QM31,
 Port3_FlushInstall.flush pending after.weights.deref=ok out ∧
 let actual : verifier.Accumulator := {after with weights:=⟨out.val,out.property⟩}
 ∀ (port : PairPort) (afterOwner : Nat),
 NIW_AlignFinishPort.Cut p port afterOwner (NJF_FinishObserved.G r loc v p actual).2.2 →
 let execution:=NJF_FinishObserved.G r loc v p actual
 Port3_NativeFinishBody.verifier.finish_relation (NIG_Slots.installed r) v p actual none=execution.1 ∧
 (∀ event∈execution.2.1,NIW_AlignFinishInvocation.Clause r event) ∧
 (∀ event∈execution.2.1,NIW_AlignFinishDomains.Inputs p v actual event) ∧
 NIW_AlignFinishPrefix.Prefix execution.2.1 ∧
 NIW_AlignFinishPairCertificate.Bound r execution.2.2 ∧
 NIW_AlignFinishInfoEvent.HasPair execution ∧ NIW_AlignFinishInfoNew.HasNew p execution ∧
 NIW_AlignFinishPort.Bound r port execution.2.2 := by
 obtain ⟨out,flush,domain⟩:=NJU_FinishDomain.reached reserved d ck proof pub hash p a after g geometry
  pending v ckSize resume start query (by omega) round0 round1 finalView windows
 refine ⟨out,flush,?_⟩
 dsimp only
 intro port afterOwner cut
 exact NJF_Root.finish r loc proof v p _ domain port afterOwner cut

#print at_call
#print axioms at_call
end NJU_FinishInstall
