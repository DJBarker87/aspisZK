import NJU_FinishInstall
import NJU_ViewWindows
set_option autoImplicit false
noncomputable section
namespace NJU_FinishCase
open Aeneas Aeneas.Std Result AspisR1 AspisR1Stage2

/-- SAME invocation case split at the literal caller View. No raw-window,
history, NoBad, proof persistence or finish-success hypothesis. This supplies
the internal domain/rejection split; it does not yet claim native bad-branch
Result/effect association or the positive TX2:065 root. -/
theorem current (reserved : Bool) (r : NP6_StdModel.Reservation)
 {H : Type} (d : aspis_core.digest.Digest32 H)
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
 let v := NJR_ViewFinish.view proof inactive
 let actual : verifier.Accumulator := {after with weights:=⟨out.val,out.property⟩}
 (NJU_CurrentWindows.Holds v ∧ NIG_FinishInput.Domain proof v p actual) ∨
 (¬ NJU_CurrentWindows.Holds v ∧
  Port4D_FinishInstall.finish (IDa_Deployed.finish r) v p actual none ≠ ok (.Ok ())) := by
 have dom:=NID_ResumeFields.returned reserved d ck proof pub hash p a ckSize resume
 have qdom:=NFW_QueryResume.domain p a dom.width
  (NID_ResumeQuery.weights a dom.weights)
  (NID_ResumeCallerDomain.wide a.rhs dom.rhs)
  (NID_ResumeCallerDomain.power a.power dom.power)
  (NID_ResumeCallerDomain.power p.rho dom.rho) start
 obtain ⟨out,flush,acc,_⟩:=NGM_FinishDomain.tx2_writeback NJJ_QueryOps.concrete proof p a after g
  geometry (NFW_QueryResume.pending a) pending qdom start query
 refine ⟨out,flush,?_⟩
 dsimp only
 rcases NJU_CurrentWindows.split (NJR_ViewFinish.view proof inactive) with good | bad
 · left
   obtain ⟨other,otherFlush,domain⟩:=NJU_FinishDomain.reached reserved d ck proof pub hash p a after g
    geometry pending (NJR_ViewFinish.view proof inactive) ckSize resume start query
    (by omega) rfl rfl rfl good
   have same : other=out := by rw [flush] at otherFlush; exact (Result.ok.inj otherFlush).symm
   subst other
   exact ⟨good,domain⟩
 · right
   obtain ⟨r0,r1,fin⟩:=NJU_ViewWindows.lengths proof inactive size
   exact ⟨bad,NJU_CurrentWindows.rejects r (NJR_ViewFinish.view proof inactive) p _ dom.variant
    acc.width r0 r1 fin bad⟩

#print current
#print axioms current
end NJU_FinishCase
