import ExtractedDigest32Callers
import ExtractedDigest32SamplerTransport
import ExtractedMaskTowerAdd

/-! Canonicality of a selected verifier-carrier QM31 produced by one actual
public-preparation semantic_validated call. The proof follows its emitted
sampler call and reuses the checked digits_total / qm31_sample_of_digits path. -/
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1PublicPreparation.SemanticCallSelectedCanonical

abbrev PublicQM := AspisR1PublicPreparation.aspis_core.field.QM31
abbrev SelectedQM := AspisR1SelectedMaskProbe.field.QM31
abbrev CurrentCanonical := AspisR1.ExtractedQM31SamplerCarrier.CurrentCanonicalQM
abbrev SelectedCanonical := AspisR1.ExtractedMaskTowerAdd.CanonicalQM

def toSelected (q : PublicQM) : SelectedQM :=
  ⟨⟨q.c0.a, q.c0.b⟩, ⟨q.c1.a, q.c1.b⟩⟩

/-- Explicit four-coordinate equality across the sampler/current and selected
nominal carriers. -/
theorem source_coordinate_copy (q : PublicQM) :
    (AspisR1.ExtractedQM31SamplerCarrier.toCurrent
      (AspisR1PublicPreparation.SamplerTransport.toOld q)).c0.a.val =
        (toSelected q).c0.a.val ∧
    (AspisR1.ExtractedQM31SamplerCarrier.toCurrent
      (AspisR1PublicPreparation.SamplerTransport.toOld q)).c0.b.val =
        (toSelected q).c0.b.val ∧
    (AspisR1.ExtractedQM31SamplerCarrier.toCurrent
      (AspisR1PublicPreparation.SamplerTransport.toOld q)).c1.a.val =
        (toSelected q).c1.a.val ∧
    (AspisR1.ExtractedQM31SamplerCarrier.toCurrent
      (AspisR1PublicPreparation.SamplerTransport.toOld q)).c1.b.val =
        (toSelected q).c1.b.val := by
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem selected_of_sampler_canonical (q : PublicQM)
    (h : CurrentCanonical
      (AspisR1.ExtractedQM31SamplerCarrier.toCurrent
        (AspisR1PublicPreparation.SamplerTransport.toOld q))) :
    SelectedCanonical (toSelected q) := by
  obtain ⟨h00, h01, h10, h11⟩ := source_coordinate_copy q
  change
    ((AspisR1.ExtractedQM31SamplerCarrier.toCurrent
        (AspisR1PublicPreparation.SamplerTransport.toOld q)).c0.a.val <
          AspisR1.ExtractedCurrentTowerAdd.P ∧
      (AspisR1.ExtractedQM31SamplerCarrier.toCurrent
        (AspisR1PublicPreparation.SamplerTransport.toOld q)).c0.b.val <
          AspisR1.ExtractedCurrentTowerAdd.P) ∧
    ((AspisR1.ExtractedQM31SamplerCarrier.toCurrent
        (AspisR1PublicPreparation.SamplerTransport.toOld q)).c1.a.val <
          AspisR1.ExtractedCurrentTowerAdd.P ∧
      (AspisR1.ExtractedQM31SamplerCarrier.toCurrent
        (AspisR1PublicPreparation.SamplerTransport.toOld q)).c1.b.val <
          AspisR1.ExtractedCurrentTowerAdd.P) at h
  rcases h with ⟨⟨hc00, hc01⟩, ⟨hc10, hc11⟩⟩
  change
    (q.c0.a.val < AspisR1.ExtractedMaskTowerAdd.P ∧
      q.c0.b.val < AspisR1.ExtractedMaskTowerAdd.P) ∧
    (q.c1.a.val < AspisR1.ExtractedMaskTowerAdd.P ∧
      q.c1.b.val < AspisR1.ExtractedMaskTowerAdd.P)
  constructor
  · constructor
    · simpa [AspisR1.ExtractedCurrentTowerAdd.P,
        AspisR1.ExtractedCurrentM31AddSub.P,
        AspisR1.ExtractedMaskTowerAdd.P,
        AspisR1.ExtractedMaskM31AddSub.P] using h00 ▸ hc00
    · simpa [AspisR1.ExtractedCurrentTowerAdd.P,
        AspisR1.ExtractedCurrentM31AddSub.P,
        AspisR1.ExtractedMaskTowerAdd.P,
        AspisR1.ExtractedMaskM31AddSub.P] using h01 ▸ hc01
  · constructor
    · simpa [AspisR1.ExtractedCurrentTowerAdd.P,
        AspisR1.ExtractedCurrentM31AddSub.P,
        AspisR1.ExtractedMaskTowerAdd.P,
        AspisR1.ExtractedMaskM31AddSub.P] using h10 ▸ hc10
    · simpa [AspisR1.ExtractedCurrentTowerAdd.P,
        AspisR1.ExtractedCurrentM31AddSub.P,
        AspisR1.ExtractedMaskTowerAdd.P,
        AspisR1.ExtractedMaskM31AddSub.P] using h11 ▸ hc11

/-- One successful semantic_validated verifier call has a canonical selected
point, with no supplied canonicality premise. -/
theorem semantic_success_selected_canonical {H : Type}
    (D : AspisR1PublicPreparation.aspis_core.Digest32 H)
    (self after : AspisR1PublicPreparation.r1_wire.SemanticTranscript H)
    (record : AspisR1PublicPreparation.r1_wire.ValidatedRecord)
    (q : PublicQM)
    (h : AspisR1PublicPreparation.r1_wire.SemanticTranscript.semantic_validated
      D self record = ok (.Ok q, after)) :
    SelectedCanonical (toSelected q) := by
  obtain ⟨_, block, _, hsample⟩ :=
    AspisR1PublicPreparation.CallerStep.semantic_success D self after record q h
  have hOld := AspisR1PublicPreparation.SamplerTransport.sample_toOld_success
    block q hsample
  have hCurrent := AspisR1.ExtractedQM31SamplerCorrect.sample_canonical_of_success
    block (AspisR1PublicPreparation.SamplerTransport.toOld q) hOld
  exact selected_of_sampler_canonical q hCurrent

#print axioms source_coordinate_copy
#print axioms selected_of_sampler_canonical
#print axioms semantic_success_selected_canonical
end AspisR1PublicPreparation.SemanticCallSelectedCanonical
