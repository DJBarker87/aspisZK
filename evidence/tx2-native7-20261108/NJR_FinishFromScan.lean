import NJR_FinishDomain
import NJR_HistoryFromScan
set_option autoImplicit false
noncomputable section
namespace NJR_FinishFromScan
open Aeneas Aeneas.Std Result AspisR1 AspisR1Stage2
/-- Internal SAME-proof history implication. Not a TX2:065 positive root: the
upstream actual successful scan and retained-byte attachment are still needed.
Every primitive finish-domain field is derived, with no independent Domain. -/
theorem reached (reserved : Bool) {H : Type} (d : aspis_core.digest.Digest32 H)
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
 (scan : Op4P_Install.sourceBody proof=ok (.Ok ())) :
 ∃ out : Slice aspis_core.field.QM31,
 Port3_FlushInstall.flush pending after.weights.deref=ok out ∧
 NIG_FinishInput.Domain proof v p {after with weights:=⟨out.val,out.property⟩} := by
 exact NJR_FinishDomain.reached reserved d ck proof pub hash p a after g geometry pending v
  ckSize resume start query (by omega) round0 round1 finalView
  (NJR_HistoryFromScan.source proof proofLength scan)

#print reached
#print axioms reached
end NJR_FinishFromScan
