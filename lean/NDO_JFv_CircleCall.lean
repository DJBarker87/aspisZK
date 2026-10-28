import NDO_JFv_CircleTotal
import NDO_JFv_TranscriptTotal
set_option autoImplicit false
namespace AspisR1.JFv_CircleCall
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation

theorem source {H : Type} (D : aspis_core.Digest32 H) (total : JFv_TranscriptTotal.Total D)
    (B : FinishModel.Boundaries) (t : r1_wire.SemanticTranscript H)
    (vr : r1_wire.ValidatedRecord) (same : vr.row=t.next_row)
    (rows : vr.row=25#u8 ∨ vr.row=26#u8) :
    ∃ point after,FinishModel.circle_validated (F3M_CircleSource.install B) D t vr=ok (.Ok point,after) ∧
      after.next_row.val=vr.row.val+1 ∧ SAP_CanonicalCarrier.CanonK point.x ∧ SAP_CanonicalCarrier.CanonK point.y := by
  have bound : vr.row.val<27 := by rcases rows with h|h <;> rw [h] <;> decide
  obtain ⟨block,after,sampled,next⟩ := JFv_TranscriptTotal.block D total t vr.row vr.framed same bound
  rcases rows with h|h
  · obtain ⟨point,circle,canon⟩ := JFv_CircleTotal.source block .First
    refine ⟨point,after,?_,next,canon⟩
    simp only [FinishModel.circle_validated,r1_wire.ValidatedRecord.impl.row,
      r1_wire.ValidatedRecord.impl.framed,h,bind_tc_ok]
    rw [h] at sampled
    rw [sampled,bind_tc_ok]
    change (do let p ← F3M_CircleSource.source block .First
               ok ((core.result.Result.Ok p : core.result.Result aspis_core.circle.SecureCirclePoint r1_wire.Error),after)) = _
    rw [circle,bind_tc_ok]
  · obtain ⟨point,circle,canon⟩ := JFv_CircleTotal.source block .Second
    refine ⟨point,after,?_,next,canon⟩
    simp only [FinishModel.circle_validated,r1_wire.ValidatedRecord.impl.row,
      r1_wire.ValidatedRecord.impl.framed,h,bind_tc_ok]
    rw [h] at sampled
    rw [sampled,bind_tc_ok]
    change (do let p ← F3M_CircleSource.source block .Second
               ok ((core.result.Result.Ok p : core.result.Result aspis_core.circle.SecureCirclePoint r1_wire.Error),after)) = _
    rw [circle,bind_tc_ok]

#print axioms source
end AspisR1.JFv_CircleCall
