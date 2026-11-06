import NKO_C07Source
import NKO_C05Source
set_option autoImplicit false
noncomputable section
namespace NKO_C07
open Aeneas Aeneas.Std Result VTop_Stages AspisR1 NJU_CommonObserved
/-- Domain and full owned input dimensions at THAT entered query call.
This consumes actual source binds; it does not assume a native input Cut. -/
theorem at_actual (wr rr : NP6_StdModel.Reservation) (merkle : Merkle) (finish : Finish)
 {H : Type} (d : aspis_core.digest.Digest32 H) (pub proof ck : Slice U8) (hash : H)
 (proofArg : Slice U8) (p : verifier.Prepared) (a : verifier.Accumulator)
 (g : Array aspis_core.field.wide_exact.WideExact 29#usize)
 (geometry : verifier.QueryGeometry) (pending : verifier.BatchedWeights)
 (reply : R (verifier.Accumulator × verifier.BatchedWeights))
 (entered : Event.query proofArg p a g geometry pending reply∈
  (run wr rr merkle finish d pub proof ck hash none).events) :
 proofArg=proof ∧ NJJ_Common.resume wr d ck proof pub .S2 hash=ok (.Ok (p,a)) ∧
 NID_ResumeFields.Domain p a ∧ a.next=10#usize ∧
 pending=NFW_QueryResume.pending a ∧ a.weights.val.length=64 ∧
 pending.raw.val.length=64 ∧ geometry.inverses.val.length=12 ∧ geometry.line_z.val.length=12 ∧
 NHT_PacketOps.powers 29#usize p.gamma=ok g := by
 obtain ⟨proofEq,resume,start,fields,pendingEq,powers⟩ := source wr rr merkle finish d pub proof ck hash _ entered
 obtain ⟨_,inverses,lines⟩ := NKO_C05.source wr rr merkle finish d pub proof ck hash _ entered
 have raw : pending.raw.val.length=64 := by
  rw [pendingEq]
  exact (NFW_QueryResume.progress a fields.width).2.1
 exact ⟨proofEq,resume,fields,start,pendingEq,fields.width,raw,inverses,lines,powers⟩
#print axioms at_actual
end NKO_C07
