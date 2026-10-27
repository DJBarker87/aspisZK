import RPt_FIq_S_RawSemanticFieldOwnerAdapter
import RPt_FIq_S_ExtractedSemanticRoundsCheckedTrace

set_option autoImplicit false
namespace AspisR1PublicPreparation.RawSemanticCheckedStepPolynomialAdapter
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation.RawSemanticFieldOwnerAdapter

abbrev MainQM := AspisR1PublicPreparation.aspis_core.field.QM31
abbrev Canonical := AspisR1PublicPreparation.RawSemanticFieldOwnerAdapter.Canonical
abbrev Outcome := AspisR1PublicPreparation.SemanticRoundsCheckedTrace.Outcome

noncomputable def exactPolynomial (coefficients : Array MainQM 28#usize) :=
  AspisR1PublicPreparation.RawSemanticPolynomialOps.polynomial
    ((mainArrayToProbe coefficients).v.map
      AspisR1.ExtractedMaskQM31Exact.decode)

/-- One checked semantic round under the concrete mapped field adapter is the
actual polynomial recurrence: its running boundary is p(0)+p(1), and its new
running value is p evaluated at the decoded round challenge.  Decoder and
canonicality facts remain explicit, so this theorem does not invent a link to
an absent external Aeneas operation body. -/
theorem checkedStep_polynomial_equations
    {H : Type} (decodeMain : (N : Usize) → AspisR1PublicPreparation.r1_wire.ValidatedRecord → Usize →
      Result (core.result.Result (Array MainQM N) AspisR1PublicPreparation.r1_wire.Error))
    (D : AspisR1PublicPreparation.aspis_core.Digest32 H)
    (pre : AspisR1PublicPreparation.r1_wire.Prefix)
    (before after : Outcome H) (round : Usize) (row : U8)
    (hstep : AspisR1PublicPreparation.SemanticRoundsCheckedTrace.CheckedStep
      (mainRoundBoundaries decodeMain) D pre before after round row)
    (hcanonicalCoeff : ∀ (record : AspisR1PublicPreparation.r1_wire.ValidatedRecord)
      (coefficients : Array MainQM 28#usize),
      decodeMain 28#usize record 0#usize =
        .ok (.Ok coefficients) →
      ∀ x ∈ (mainArrayToProbe coefficients).v, Canonical x)
    (hcanonicalChallenge : ∀ (record : AspisR1PublicPreparation.r1_wire.ValidatedRecord)
      (q : MainQM),
      AspisR1PublicPreparation.r1_wire.SemanticTranscript.semantic_validated D
        before.2.2 record = .ok (.Ok q, after.2.2) → Canonical (mainToProbe q))
    (hindex : ∀ q : MainQM,
      Array.index_usize (before.2.1.set round q) round = .ok q) :
    ∃ record coefficients q,
      AspisR1PublicPreparation.r1_wire.Prefix.validated_record pre row = .ok (.Ok record) ∧
      decodeMain 28#usize record 0#usize = .ok (.Ok coefficients) ∧
      AspisR1PublicPreparation.r1_wire.SemanticTranscript.semantic_validated D
        before.2.2 record = .ok (.Ok q, after.2.2) ∧
      after.2.1 = before.2.1.set round q ∧
      (exactPolynomial coefficients).eval 0 + (exactPolynomial coefficients).eval 1 =
        AspisR1.ExtractedMaskQM31Exact.decode (mainToProbe before.1) ∧
      AspisR1.ExtractedMaskQM31Exact.decode (mainToProbe after.1) =
        (exactPolynomial coefficients).eval
          (AspisR1.ExtractedMaskQM31Exact.decode (mainToProbe q)) := by
  change ∃ record coefficients boundary q, _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ at hstep
  rcases hstep with ⟨record, coefficients, boundary, q,
    hrecord, hdecode, hboundary, hneq, hboundaryEq, hsemantic, hset, hvalue⟩
  have hcoeff := hcanonicalCoeff record coefficients hdecode
  obtain ⟨mappedBoundary, hboundaryRun, hboundaryCanon, hboundaryEval⟩ :=
    extractedMainBoundary_refines coefficients hcoeff
  have hboundaryRun' : extractedMainBoundary coefficients = .ok boundary := by
    simpa [mainRoundBoundaries] using hboundary
  have hmappedBoundaryEq : mappedBoundary = boundary :=
    Result.ok.inj (hboundaryRun.symm.trans hboundaryRun')
  have hchallengeCanon := hcanonicalChallenge record q hsemantic
  have hroundIndex := hindex q
  obtain ⟨mappedValue, hvalueRun, hvalueCanon, hvalueEval⟩ :=
    extractedMainValueAt_refines coefficients (before.2.1.set round q) round q
      (by simpa [hset] using hroundIndex) hchallengeCanon hcoeff
  rw [hset] at hvalue
  have hvalueRun' : extractedMainValueAt coefficients (before.2.1.set round q) round = .ok after.1 := by
    simpa [mainRoundBoundaries] using hvalue
  have hmappedValueEq : mappedValue = after.1 :=
    Result.ok.inj (hvalueRun.symm.trans hvalueRun')
  refine ⟨record, coefficients, q, hrecord, hdecode, hsemantic, hset, ?_, ?_⟩
  · calc
      (exactPolynomial coefficients).eval 0 + (exactPolynomial coefficients).eval 1 =
          AspisR1.ExtractedMaskQM31Exact.decode (mainToProbe mappedBoundary) := by
            exact hboundaryEval.symm
      _ = AspisR1.ExtractedMaskQM31Exact.decode (mainToProbe boundary) := by
            rw [hmappedBoundaryEq]
      _ = AspisR1.ExtractedMaskQM31Exact.decode (mainToProbe before.1) := by
            rw [hboundaryEq]
  · calc
      AspisR1.ExtractedMaskQM31Exact.decode (mainToProbe after.1) =
          (exactPolynomial coefficients).eval
            (AspisR1.ExtractedMaskQM31Exact.decode (mainToProbe q)) := by
              rw [← hmappedValueEq]
              exact hvalueEval
      _ = (exactPolynomial coefficients).eval
            (AspisR1.ExtractedMaskQM31Exact.decode (mainToProbe q)) := rfl

#print axioms checkedStep_polynomial_equations
end AspisR1PublicPreparation.RawSemanticCheckedStepPolynomialAdapter
