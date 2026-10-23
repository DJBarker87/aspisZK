import SemanticRoundAlphaSelectedCanonical

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1SemanticRoundCurrentCanonicalBridgeV1

abbrev PublicQM := AspisR1PublicPreparation.aspis_core.field.QM31
abbrev SelectedCanonical := AspisR1PublicPreparation.SemanticCallSelectedCanonical.SelectedCanonical
abbrev CurrentCanonical := AspisR1.ExtractedQM31SamplerCarrier.CurrentCanonicalQM

/-- Convert the selected verifier-carrier canonical predicate to the current
sampler carrier for the same four source coordinates. -/
theorem selected_alpha_value_current_canonical (q : PublicQM)
    (h : SelectedCanonical
      (AspisR1PublicPreparation.SemanticCallSelectedCanonical.toSelected q)) :
    CurrentCanonical
      (AspisR1.ExtractedQM31SamplerCarrier.toCurrent
        (AspisR1PublicPreparation.SamplerTransport.toOld q)) := by
  change
    ((q.c0.a.val < AspisR1.ExtractedMaskTowerAdd.P ∧
      q.c0.b.val < AspisR1.ExtractedMaskTowerAdd.P) ∧
     (q.c1.a.val < AspisR1.ExtractedMaskTowerAdd.P ∧
      q.c1.b.val < AspisR1.ExtractedMaskTowerAdd.P)) at h
  change
    ((q.c0.a.val < AspisR1.ExtractedCurrentTowerAdd.P ∧
      q.c0.b.val < AspisR1.ExtractedCurrentTowerAdd.P) ∧
     (q.c1.a.val < AspisR1.ExtractedCurrentTowerAdd.P ∧
      q.c1.b.val < AspisR1.ExtractedCurrentTowerAdd.P))
  rcases h with ⟨⟨h00, h01⟩, ⟨h10, h11⟩⟩
  constructor
  · constructor
    · simpa [AspisR1.ExtractedMaskTowerAdd.P,
        AspisR1.ExtractedMaskM31AddSub.P, AspisR1.ExtractedCurrentTowerAdd.P,
        AspisR1.ExtractedCurrentM31AddSub.P] using h00
    · simpa [AspisR1.ExtractedMaskTowerAdd.P,
        AspisR1.ExtractedMaskM31AddSub.P, AspisR1.ExtractedCurrentTowerAdd.P,
        AspisR1.ExtractedCurrentM31AddSub.P] using h01
  · constructor
    · simpa [AspisR1.ExtractedMaskTowerAdd.P,
        AspisR1.ExtractedMaskM31AddSub.P, AspisR1.ExtractedCurrentTowerAdd.P,
        AspisR1.ExtractedCurrentM31AddSub.P] using h10
    · simpa [AspisR1.ExtractedMaskTowerAdd.P,
        AspisR1.ExtractedMaskM31AddSub.P, AspisR1.ExtractedCurrentTowerAdd.P,
        AspisR1.ExtractedCurrentM31AddSub.P] using h11

/-- Every element returned in the actual ten-round model alpha array is
canonical in the current sampler carrier. The induction over semantic calls
is reused from `run_values_canonical`; this does not claim that the Rust caller
has been refined to `RoundModel.rounds`. -/
theorem verifier_round_alpha_current_canonical {H : Type}
    (B : AspisR1PublicPreparation.RoundModel.Boundaries)
    (D : AspisR1PublicPreparation.aspis_core.Digest32 H)
    (pre : AspisR1PublicPreparation.r1_wire.Prefix)
    (self after : AspisR1PublicPreparation.r1_wire.SemanticTranscript H)
    (running : PublicQM) (alpha : Array PublicQM 10#usize)
    (h : AspisR1PublicPreparation.RoundModel.rounds B D pre self =
      .ok (.Ok (running, alpha, after))) :
    ∀ i : Fin 10,
      CurrentCanonical
        (AspisR1.ExtractedQM31SamplerCarrier.toCurrent
          (AspisR1PublicPreparation.SamplerTransport.toOld
            (alpha.val[i.val]'(by simpa [alpha.property] using i.isLt)))) := by
  have hselected :=
    AspisR1PublicPreparation.SemanticRoundAlphaSelectedCanonical.verifier_round_alpha_canonical
      B D pre self after running alpha h
  intro i
  exact selected_alpha_value_current_canonical _ (hselected i)

#print axioms selected_alpha_value_current_canonical
#print axioms verifier_round_alpha_current_canonical

end AspisR1SemanticRoundCurrentCanonicalBridgeV1
