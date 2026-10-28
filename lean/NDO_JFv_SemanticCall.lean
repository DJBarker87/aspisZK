import NDO_JFv_TranscriptTotal
set_option autoImplicit false
namespace AspisR1.JFv_SemanticCall
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation

theorem success {H : Type} (D : aspis_core.Digest32 H) (total : JFv_TranscriptTotal.Total D)
    (t : r1_wire.SemanticTranscript H) (vr : r1_wire.ValidatedRecord)
    (same : vr.row=t.next_row) (bound : vr.row.val<25) :
    ∃ q after,r1_wire.SemanticTranscript.semantic_validated D t vr=ok (.Ok q,after) ∧
      after.next_row.val=vr.row.val+1 ∧ JFv_RoundArithmetic.Canonical q := by
  obtain ⟨block,after,call,next⟩ := JFv_TranscriptTotal.block D total t vr.row vr.framed same (by omega)
  obtain ⟨q,sampled,canonical,_⟩ := SamplerTransport.sample_total block
  refine ⟨q,after,?_,next,?_⟩
  · simp only [r1_wire.SemanticTranscript.semantic_validated,r1_wire.ValidatedRecord.impl.row,
      r1_wire.ValidatedRecord.impl.framed,bind_tc_ok]
    rw [if_neg (by change ¬ vr.row.val>24;omega)]
    rw [call,bind_tc_ok]
    change (do let value ← AspisR1PublicPreparation.sampler.qm31_sample block; ok ((core.result.Result.Ok value : core.result.Result aspis_core.field.QM31 r1_wire.Error),after)) = _
    rw [sampled,bind_tc_ok]
  · change (_ ∧ _) ∧ (_ ∧ _)
    exact ⟨⟨canonical.1.1,canonical.1.2⟩,canonical.2⟩

#print axioms success
end AspisR1.JFv_SemanticCall
