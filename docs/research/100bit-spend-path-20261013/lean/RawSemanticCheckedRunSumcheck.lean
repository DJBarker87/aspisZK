import RawSemanticCheckedRunPolynomialAdapter
import RawSemanticPolynomialDegree28

set_option autoImplicit false
namespace AspisR1PublicPreparation.RawSemanticCheckedRunSumcheck
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation.RawSemanticFieldOwnerAdapter
open AspisR1PublicPreparation.RawSemanticCheckedStepPolynomialAdapter
open AspisR1PublicPreparation.RawSemanticCheckedRunPolynomialAdapter
open AspisR1PublicPreparation.RawSemanticPolynomialDegree28

abbrev MainQM := AspisR1PublicPreparation.aspis_core.field.QM31
abbrev Outcome (H : Type) := AspisR1PublicPreparation.SemanticRoundsCheckedTrace.Outcome H

/-- A single retained source round together with its degree-27 guarantee.
The endpoint and challenge-evaluation equations are exactly those from the
checked machine-operation adapter. -/
def PolynomialSumcheckStep {H : Type}
    (D : AspisR1PublicPreparation.aspis_core.Digest32 H)
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
        (AspisR1.ExtractedMaskQM31Exact.decode (mainToProbe q)) ∧
    (exactPolynomial coefficients).natDegree ≤ 27

/-- All ten checked semantic rounds, with one actual degree-27 polynomial per
round. The first boundary equation targets the decoded initial claim; the next
nine equations target the previous round's running claim. The final node carries
the tenth challenge evaluation. External links from decoded endpoints to
`maskSum`/`terminalZ` remain separate named interfaces. -/
inductive PolynomialSumcheckRun {H : Type}
    (D : AspisR1PublicPreparation.aspis_core.Digest32 H)
    (pre : AspisR1PublicPreparation.r1_wire.Prefix) :
    List (Usize × U8) → Outcome H → Outcome H → Prop
  | nil (out : Outcome H) : PolynomialSumcheckRun D pre [] out out
  | cons {round : Usize} {row : U8} {rest : List (Usize × U8)}
      {before mid after : Outcome H}
      (step : PolynomialSumcheckStep D pre before mid round row)
      (tail : PolynomialSumcheckRun D pre rest mid after) :
      PolynomialSumcheckRun D pre ((round, row) :: rest) before after

theorem polynomialCheckedRun_to_sumcheckRun {H : Type}
    {D : AspisR1PublicPreparation.aspis_core.Digest32 H}
    {pre : AspisR1PublicPreparation.r1_wire.Prefix}
    {events : List (Usize × U8)} {initial final : Outcome H}
    (hrun : PolynomialCheckedRun D pre events initial final) :
    PolynomialSumcheckRun D pre events initial final := by
  induction hrun with
  | nil out => exact .nil out
  | @cons round row rest before mid after hstep htail ih =>
      rcases hstep with ⟨record, coefficients, q, hrecord, hsemantic, hset, hboundary, hvalue⟩
      exact .cons
        ⟨record, coefficients, q, hrecord, hsemantic, hset, hboundary, hvalue,
          exactPolynomial_natDegree_le_27 coefficients⟩ ih

/-- The first retained polynomial has endpoint sum equal to the decoded initial
running claim. This deliberately does not identify that claim with `maskSum`;
that production/source boundary is kept explicit. -/
theorem sumcheck_initial_boundary {H : Type}
    {D : AspisR1PublicPreparation.aspis_core.Digest32 H}
    {pre : AspisR1PublicPreparation.r1_wire.Prefix}
    {events : List (Usize × U8)} {initial final : Outcome H}
    (hrun : PolynomialSumcheckRun D pre events initial final)
    (hne : events ≠ []) :
    ∃ (record : AspisR1PublicPreparation.r1_wire.ValidatedRecord)
      (coefficients : Array MainQM 28#usize) (q : MainQM),
      AspisR1PublicPreparation.r1_wire.Prefix.validated_record pre events.head!.2 =
        .ok (.Ok record) ∧
      (exactPolynomial coefficients).eval 0 + (exactPolynomial coefficients).eval 1 =
        AspisR1.ExtractedMaskQM31Exact.decode (mainToProbe initial.1) := by
  cases hrun with
  | nil out => cases hne rfl
  | @cons round row rest before mid after hstep htail =>
      rcases hstep with ⟨record, coefficients, q, hrecord, hsemantic, hset, hboundary, hvalue, hdegree⟩
      refine ⟨record, coefficients, q, ?_, hboundary⟩
      simpa using hrecord

/-- The last retained polynomial evaluates to the final decoded running claim
at its actual transcript challenge. -/
theorem sumcheck_final_evaluation {H : Type}
    {D : AspisR1PublicPreparation.aspis_core.Digest32 H}
    {pre : AspisR1PublicPreparation.r1_wire.Prefix}
    {events : List (Usize × U8)} {initial final : Outcome H}
    (hrun : PolynomialSumcheckRun D pre events initial final)
    (hne : events ≠ []) :
    ∃ (record : AspisR1PublicPreparation.r1_wire.ValidatedRecord)
      (coefficients : Array MainQM 28#usize) (q : MainQM)
      (before : Outcome H) (round : Usize) (row : U8),
      AspisR1PublicPreparation.r1_wire.Prefix.validated_record pre row = .ok (.Ok record) ∧
      AspisR1.ExtractedMaskQM31Exact.decode (mainToProbe final.1) =
        (exactPolynomial coefficients).eval
          (AspisR1.ExtractedMaskQM31Exact.decode (mainToProbe q)) := by
  induction hrun with
  | nil out => cases hne rfl
  | @cons round row rest before mid after hstep htail ih =>
      cases rest with
      | nil =>
          cases htail
          rcases hstep with ⟨record, coefficients, q, hrecord, hsemantic, hset,
            hboundary, hvalue, hdegree⟩
          exact ⟨record, coefficients, q, before, round, row, hrecord, hvalue⟩
      | cons next tail =>
          have htailne : next :: tail ≠ [] := by simp
          exact ih htailne


/-- The actual checked ten-row schedule has a degree-27 sumcheck package under
exactly the same decoder-canonicality and challenge/index premises used by the
single-step adapter. -/
theorem checkedSchedule_to_sumcheckRun {H : Type}
    (decodeMain : (N : Usize) → AspisR1PublicPreparation.r1_wire.ValidatedRecord → Usize →
      Result (core.result.Result (Array MainQM N) AspisR1PublicPreparation.r1_wire.Error))
    (D : AspisR1PublicPreparation.aspis_core.Digest32 H)
    (pre : AspisR1PublicPreparation.r1_wire.Prefix)
    (initial final : Outcome H)
    (hrun : AspisR1PublicPreparation.SemanticRoundsCheckedTrace.CheckedRun
      (mainRoundBoundaries decodeMain) D pre
      AspisR1PublicPreparation.SemanticRoundsCheckedTrace.schedule initial final)
    (hcanonicalCoeff : ∀ (record : AspisR1PublicPreparation.r1_wire.ValidatedRecord)
      (coefficients : Array MainQM 28#usize),
      decodeMain 28#usize record 0#usize = .ok (.Ok coefficients) →
      ∀ x ∈ (mainArrayToProbe coefficients).v, AspisR1PublicPreparation.RawSemanticFieldOwnerAdapter.Canonical x)
    (hcanonicalChallenge : ∀ (transcriptBefore transcriptAfter :
      AspisR1PublicPreparation.r1_wire.SemanticTranscript H)
      (record : AspisR1PublicPreparation.r1_wire.ValidatedRecord) (q : MainQM),
      AspisR1PublicPreparation.r1_wire.SemanticTranscript.semantic_validated D
        transcriptBefore record = .ok (.Ok q, transcriptAfter) → AspisR1PublicPreparation.RawSemanticFieldOwnerAdapter.Canonical (mainToProbe q))
    (hindex : ∀ {before after : Outcome H} {round : Usize} {row : U8},
      AspisR1PublicPreparation.SemanticRoundsCheckedTrace.CheckedStep
        (mainRoundBoundaries decodeMain) D pre before after round row →
      ∀ q : MainQM, Array.index_usize (before.2.1.set round q) round = .ok q) :
    PolynomialSumcheckRun D pre AspisR1PublicPreparation.SemanticRoundsCheckedTrace.schedule
      initial final := by
  apply polynomialCheckedRun_to_sumcheckRun
  exact checkedRun_to_polynomialCheckedRun decodeMain D pre
    AspisR1PublicPreparation.SemanticRoundsCheckedTrace.schedule initial final hrun
    hcanonicalCoeff hcanonicalChallenge hindex

theorem checked_schedule_length :
    AspisR1PublicPreparation.SemanticRoundsCheckedTrace.schedule.length = 10 := rfl

#print axioms checkedSchedule_to_sumcheckRun
#print axioms checked_schedule_length
#print axioms polynomialCheckedRun_to_sumcheckRun
#print axioms sumcheck_initial_boundary
#print axioms sumcheck_final_evaluation
end AspisR1PublicPreparation.RawSemanticCheckedRunSumcheck
