import RawSemanticCheckedStepPolynomialAdapter
import ExtractedSemanticRoundsCheckedTrace

set_option autoImplicit false
namespace AspisR1PublicPreparation.RawSemanticCheckedRunPolynomialAdapter
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation.RawSemanticFieldOwnerAdapter
open AspisR1PublicPreparation.RawSemanticCheckedStepPolynomialAdapter

abbrev MainQM := AspisR1PublicPreparation.aspis_core.field.QM31
abbrev Canonical := AspisR1PublicPreparation.RawSemanticFieldOwnerAdapter.Canonical
abbrev Outcome := AspisR1PublicPreparation.SemanticRoundsCheckedTrace.Outcome

/-- A checked step with the field operation projected to its exact polynomial
boundary and challenge-value equations. -/
def PolynomialCheckedStep {H : Type} (D : AspisR1PublicPreparation.aspis_core.Digest32 H)
    (pre : AspisR1PublicPreparation.r1_wire.Prefix)
    (before after : Outcome H) (round : Usize) (row : U8) : Prop :=
  ∃ (record : AspisR1PublicPreparation.r1_wire.ValidatedRecord)
    (coefficients : Array MainQM 28#usize) (q : MainQM),
    AspisR1PublicPreparation.r1_wire.Prefix.validated_record pre row = .ok (.Ok record) ∧
    AspisR1PublicPreparation.r1_wire.SemanticTranscript.semantic_validated D
      before.2.2 record = .ok (.Ok q, after.2.2) ∧
    after.2.1 = before.2.1.set round q ∧
    (exactPolynomial coefficients).eval 0 + (exactPolynomial coefficients).eval 1 =
      AspisR1.ExtractedMaskQM31Exact.decode (mainToProbe before.1) ∧
    AspisR1.ExtractedMaskQM31Exact.decode (mainToProbe after.1) =
      (exactPolynomial coefficients).eval
        (AspisR1.ExtractedMaskQM31Exact.decode (mainToProbe q))

/-- The ten-step checked trace induces ten genuine polynomial recurrence
steps.  Premises state exactly the row-decoder canonicality, transcript
challenge canonicality, and in-range updated-alpha lookup needed by the
machine-operation refinement; no semanticChecks conclusion is assumed. -/
inductive PolynomialCheckedRun {H : Type}
    (D : AspisR1PublicPreparation.aspis_core.Digest32 H)
    (pre : AspisR1PublicPreparation.r1_wire.Prefix) :
    List (Usize × U8) → Outcome H → Outcome H → Prop
  | nil (out : Outcome H) : PolynomialCheckedRun D pre [] out out
  | cons {round : Usize} {row : U8} {rest : List (Usize × U8)}
      {before mid after : Outcome H}
      (step : PolynomialCheckedStep D pre before mid round row)
      (tail : PolynomialCheckedRun D pre rest mid after) :
      PolynomialCheckedRun D pre ((round, row) :: rest) before after

theorem checkedRun_to_polynomialCheckedRun {H : Type}
    (decodeMain : (N : Usize) → AspisR1PublicPreparation.r1_wire.ValidatedRecord → Usize →
      Result (core.result.Result (Array MainQM N) AspisR1PublicPreparation.r1_wire.Error))
    (D : AspisR1PublicPreparation.aspis_core.Digest32 H)
    (pre : AspisR1PublicPreparation.r1_wire.Prefix)
    (events : List (Usize × U8)) (initial final : Outcome H)
    (hrun : AspisR1PublicPreparation.SemanticRoundsCheckedTrace.CheckedRun
      (mainRoundBoundaries decodeMain) D pre events initial final)
    (hcanonicalCoeff : ∀ (record : AspisR1PublicPreparation.r1_wire.ValidatedRecord)
      (coefficients : Array MainQM 28#usize),
      decodeMain 28#usize record 0#usize = .ok (.Ok coefficients) →
      ∀ x ∈ (mainArrayToProbe coefficients).v, Canonical x)
    (hcanonicalChallenge : ∀ (transcriptBefore transcriptAfter :
      AspisR1PublicPreparation.r1_wire.SemanticTranscript H)
      (record : AspisR1PublicPreparation.r1_wire.ValidatedRecord) (q : MainQM),
      AspisR1PublicPreparation.r1_wire.SemanticTranscript.semantic_validated D
        transcriptBefore record = .ok (.Ok q, transcriptAfter) → Canonical (mainToProbe q))
    (hindex : ∀ {before after : Outcome H} {round : Usize} {row : U8},
      AspisR1PublicPreparation.SemanticRoundsCheckedTrace.CheckedStep
        (mainRoundBoundaries decodeMain) D pre before after round row →
      ∀ q : MainQM,
        Array.index_usize (before.2.1.set round q) round = .ok q) :
    PolynomialCheckedRun D pre events initial final := by
  induction hrun with
  | nil out => exact .nil out
  | @cons round row rest before mid after hstep htail ih =>
      apply PolynomialCheckedRun.cons
      · rcases checkedStep_polynomial_equations decodeMain D pre before mid round row hstep
          hcanonicalCoeff
          (fun record q hsem => hcanonicalChallenge before.2.2 mid.2.2 record q hsem)
          (hindex hstep) with
          ⟨record, coefficients, q, hrecord, hdecode, hsemantic, hset, hboundary, hvalue⟩
        exact ⟨record, coefficients, q, hrecord, hsemantic, hset, hboundary, hvalue⟩
      · exact ih

#print axioms checkedRun_to_polynomialCheckedRun
end AspisR1PublicPreparation.RawSemanticCheckedRunPolynomialAdapter
