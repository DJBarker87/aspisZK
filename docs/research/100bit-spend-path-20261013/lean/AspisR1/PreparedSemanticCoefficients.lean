import SemanticPackedSixFamiliesActualPreparationClosed
import SemanticCompositionCoefficients

/-! Exact semantic coefficients from the same successful public preparation.
No independently assumed packed-output or digest-bound equations. -/
set_option autoImplicit false
namespace AspisR1.PreparedSemanticCoefficients
noncomputable section
open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe
open AspisR1.SemanticCompositionCoefficients
open AspisR1TerminalDigestBindingCandidate.SemanticPublicPreparationCopy

theorem actual_coefficients
    (point : Array QM 10#usize) (selectors : Selectors)
    (s : AspisR1TerminalDecoder.PublicBinding.Statement) (openings : Openings)
    (hpoint : CanonicalArray point)
    (hbox : pool_v1.pair_forest_copy_terminal.Selectors.boxed_at_point point = .ok selectors)
    (hz : CanonicalArray openings.z) (hsucc : CanonicalArray openings.succ_z)
    (hxor : CanonicalArray openings.xor12_z)
    {H : Type} (D : AspisR1PublicPreparation.aspis_core.Digest32 H)
    (hash : H) (c1 : Array U8 32#usize)
    (outTranscript : AspisR1PublicPreparation.r1_wire.SemanticTranscript H)
    (hprep : AspisR1PublicPreparation.r1_semantic.public_transcript D
      (AspisR1PublicPreparation.PreparationBinding.preparationPublic s)
      hash c1 = Result.ok (.Ok outTranscript)) :
    ∃ semantic : Array QM 24#usize,
      AspisR1SemanticPackedBoundedCandidate.pool_v1.pair_forest_semantic_terminal.semantic_packed
        (copyFromStatement s) openings selectors = .ok semantic ∧
      CanonicalArray semantic ∧
      ∀ i : Fin 24, AspisR1.PreweightedLoopModel.decoded semantic i =
        semanticLane24 (copyFromStatement s) openings point i := by
  obtain ⟨semantic, hrun, hcan, hwide⟩ :=
    AspisR1.SemanticPackedSixFamiliesActualPreparation.actual_semantic_packed_of_preparation
      point selectors s openings hpoint hbox hz hsucc hxor D hash c1 outTranscript hprep
  exact ⟨semantic, hrun, hcan,
    coefficients_of_packed_equations semantic point (copyFromStatement s) openings hwide⟩

#print axioms actual_coefficients
end
end AspisR1.PreparedSemanticCoefficients
