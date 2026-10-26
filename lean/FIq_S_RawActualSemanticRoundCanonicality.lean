import FIq_S_RawGeneratedSemanticRoundPolynomialAdapter
import FIq_S_RawActualDecodeKMainAdapter
import SemanticCallSelectedCanonical

set_option autoImplicit false
namespace AspisR1PublicPreparation.RawActualSemanticRoundCanonicality

open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation.RawSemanticFieldOwnerAdapter
open AspisR1PublicPreparation.RawGeneratedSemanticRoundPolynomialAdapter

abbrev MainQM := AspisR1PublicPreparation.RawGeneratedSemanticRoundPolynomialAdapter.MainQM

abbrev Outcome := AspisR1PublicPreparation.SemanticRoundsCheckedTrace.Outcome

def actualRoundBoundaries : AspisR1PublicPreparation.RoundModel.Boundaries :=
  generatedRoundBoundaries AspisR1PublicPreparation.RawActualDecodeKMainAdapter.decodeMain

theorem checkedStep_polynomial_equations_actual
    {H : Type} (D : AspisR1PublicPreparation.aspis_core.Digest32 H)
    (pre : AspisR1PublicPreparation.r1_wire.Prefix)
    (before after : Outcome H) (round : Usize) (row : U8)
    (hstep : AspisR1PublicPreparation.SemanticRoundsCheckedTrace.CheckedStep
      actualRoundBoundaries D pre before after round row)
    (hindex : ∀ q : MainQM,
      Array.index_usize (before.2.1.set round q) round = .ok q) :
    ∃ record coefficients q,
      AspisR1PublicPreparation.r1_wire.Prefix.validated_record pre row = .ok (.Ok record) ∧
      AspisR1PublicPreparation.RawActualDecodeKMainAdapter.decodeMain
        28#usize record 0#usize = .ok (.Ok coefficients) ∧
      AspisR1PublicPreparation.r1_wire.SemanticTranscript.semantic_validated
        D before.2.2 record = .ok (.Ok q, after.2.2) ∧
      after.2.1 = before.2.1.set round q ∧
      (AspisR1PublicPreparation.RawSemanticCheckedStepPolynomialAdapter.exactPolynomial coefficients).eval 0 + (AspisR1PublicPreparation.RawSemanticCheckedStepPolynomialAdapter.exactPolynomial coefficients).eval 1 =
        AspisR1.ExtractedMaskQM31Exact.decode (mainToProbe before.1) ∧
      AspisR1.ExtractedMaskQM31Exact.decode (mainToProbe after.1) =
        (AspisR1PublicPreparation.RawSemanticCheckedStepPolynomialAdapter.exactPolynomial coefficients).eval
          (AspisR1.ExtractedMaskQM31Exact.decode (mainToProbe q)) := by
  apply checkedStep_polynomial_equations
    AspisR1PublicPreparation.RawActualDecodeKMainAdapter.decodeMain
    D pre before after round row
  · simpa [actualRoundBoundaries] using hstep
  · intro record coefficients hdecode
    intro x hx
    obtain ⟨q, hq, hqx⟩ := List.mem_map.mp hx
    subst x
    exact AspisR1PublicPreparation.RawActualDecodeKMainAdapter.decodeMain_success_members_canonical
      28#usize record 0#usize coefficients hdecode q hq
  · intro record q hsemantic
    have hselected :=
      AspisR1PublicPreparation.SemanticCallSelectedCanonical.semantic_success_selected_canonical
        D before.2.2 after.2.2 record q hsemantic
    simpa [AspisR1PublicPreparation.SemanticCallSelectedCanonical.toSelected,
      AspisR1PublicPreparation.RawSemanticFieldOwnerAdapter.mainToProbe] using hselected
  · exact hindex

#print axioms checkedStep_polynomial_equations_actual
end AspisR1PublicPreparation.RawActualSemanticRoundCanonicality
