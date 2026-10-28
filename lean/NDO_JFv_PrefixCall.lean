import NDO_JFv_SemanticCall
set_option autoImplicit false
namespace AspisR1.JFv_PrefixCall
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation

theorem success {H : Type} (D : aspis_core.Digest32 H) (total : JFv_TranscriptTotal.Total D)
    (pre : r1_wire.Prefix) (t : r1_wire.SemanticTranscript H) (row : U8)
    (same : row=t.next_row) (bound : row.val<25) :
    ∃ vr q after,r1_wire.Prefix.validated_record pre row=ok (.Ok vr) ∧
      vr.row=row ∧ r1_wire.SemanticTranscript.semantic_validated D t vr=ok (.Ok q,after) ∧
      after.next_row.val=row.val+1 ∧ JFv_RoundArithmetic.Canonical q := by
  obtain ⟨frame,read⟩ := JFv_PrefixRecord.record pre row (by omega)
  let vr : r1_wire.ValidatedRecord := ⟨row,frame⟩
  have call : r1_wire.Prefix.validated_record pre row=ok (.Ok vr) := by
    simp only [r1_wire.Prefix.validated_record,read,bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch]
    rfl
  obtain ⟨q,after,sampled,next,canon⟩ := JFv_SemanticCall.success D total t vr same bound
  exact ⟨vr,q,after,call,rfl,sampled,next,canon⟩

#print axioms success
end AspisR1.JFv_PrefixCall
