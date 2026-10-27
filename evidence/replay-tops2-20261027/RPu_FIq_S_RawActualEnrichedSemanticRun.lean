import RPu_FIq_S_RawActualSemanticRoundCanonicality
import RPz7_ExtractedSemanticRoundsReachability
import RPu_FIq_S_RawSemanticPolynomialDegree28

set_option autoImplicit false
namespace AspisR1PublicPreparation.RawActualEnrichedSemanticRun

open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation.RawSemanticFieldOwnerAdapter
open AspisR1PublicPreparation.RawActualSemanticRoundCanonicality

private theorem schedule_round_lt_ten {round : Usize} {row : U8}
    (h : (round, row) ∈ AspisR1PublicPreparation.SemanticRoundsCheckedTrace.schedule) :
    round.val < 10 := by
  have hm : round.val ∈ List.map (fun e : Usize × U8 => e.1.val)
      AspisR1PublicPreparation.SemanticRoundsCheckedTrace.schedule := by
    exact List.mem_map.mpr ⟨(round, row), h, rfl⟩
  have hv : round.val ∈ [0, 1, 2, 3, 4, 5, 6, 7, 8, 9] := by
    simpa [AspisR1PublicPreparation.SemanticRoundsCheckedTrace.schedule] using hm
  simp only [List.mem_cons, List.not_mem_nil] at hv
  simp at hv
  rcases hv with h | h | h | h | h | h | h | h | h | h
  all_goals omega

abbrev MainQM := AspisR1PublicPreparation.RawGeneratedSemanticRoundPolynomialAdapter.MainQM
abbrev Outcome := AspisR1PublicPreparation.SemanticRoundsCheckedTrace.Outcome

/-- One polynomial recurrence step tied to a reached source step. The retained
`decodeMain` success and semantic call are part of the witness, so neither the
coefficients nor the challenge can be chosen independently of execution. -/
def Step {H : Type} (D : AspisR1PublicPreparation.aspis_core.Digest32 H)
    (pre : AspisR1PublicPreparation.r1_wire.Prefix)
    (before after : Outcome H) (round : Usize) (row : U8) : Prop :=
  ∃ record coefficients q,
    AspisR1PublicPreparation.r1_wire.Prefix.validated_record pre row = .ok (.Ok record) ∧
    AspisR1PublicPreparation.RawActualDecodeKMainAdapter.decodeMain
      28#usize record 0#usize = .ok (.Ok coefficients) ∧
    AspisR1PublicPreparation.r1_wire.SemanticTranscript.semantic_validated
      D before.2.2 record = .ok (.Ok q, after.2.2) ∧
    after.2.1 = before.2.1.set round q ∧
    (AspisR1PublicPreparation.RawSemanticCheckedStepPolynomialAdapter.exactPolynomial
      coefficients).eval 0 +
      (AspisR1PublicPreparation.RawSemanticCheckedStepPolynomialAdapter.exactPolynomial
        coefficients).eval 1 =
      AspisR1.ExtractedMaskQM31Exact.decode (mainToProbe before.1) ∧
    AspisR1.ExtractedMaskQM31Exact.decode (mainToProbe after.1) =
      (AspisR1PublicPreparation.RawSemanticCheckedStepPolynomialAdapter.exactPolynomial
        coefficients).eval
        (AspisR1.ExtractedMaskQM31Exact.decode (mainToProbe q)) ∧
    (AspisR1PublicPreparation.RawSemanticCheckedStepPolynomialAdapter.exactPolynomial
      coefficients).natDegree ≤ 27

/-- Ordered collection of actual reached steps. The original CheckedStep is
not abstracted away: its decode, boundary comparator, semantic operation,
array update, and value call are retained alongside the polynomial equations. -/
inductive Run {H : Type}
    (D : AspisR1PublicPreparation.aspis_core.Digest32 H)
    (pre : AspisR1PublicPreparation.r1_wire.Prefix) :
    List (Usize × U8) → Outcome H → Outcome H → Prop
  | nil (out : Outcome H) : Run D pre [] out out
  | cons {round : Usize} {row : U8} {rest : List (Usize × U8)}
      {before mid after : Outcome H}
      (sourceStep : AspisR1PublicPreparation.SemanticRoundsCheckedTrace.CheckedStep
        actualRoundBoundaries D pre before mid round row)
      (polynomialStep : Step D pre before mid round row)
      (tail : Run D pre rest mid after) :
      Run D pre ((round, row) :: rest) before after

theorem checkedRun_to_run {H : Type}
    (D : AspisR1PublicPreparation.aspis_core.Digest32 H)
    (pre : AspisR1PublicPreparation.r1_wire.Prefix)
    (events : List (Usize × U8)) (initial final : Outcome H)
    (hrun : AspisR1PublicPreparation.SemanticRoundsCheckedTrace.CheckedRun
      actualRoundBoundaries D pre events initial final)
    (hevents : ∀ e ∈ events,
      e ∈ AspisR1PublicPreparation.SemanticRoundsCheckedTrace.schedule) :
    Run D pre events initial final := by
  induction hrun with
  | nil out => exact .nil out
  | @cons round row rest before mid after hstep htail ih =>
      have hsched := hevents (round, row) (by simp)
      have hround := schedule_round_lt_ten hsched
      have hindex : ∀ q : MainQM,
          Array.index_usize (before.2.1.set round q) round = .ok q := by
        intro q
        unfold Array.index_usize
        simp [Array.set, hround]
      rcases checkedStep_polynomial_equations_actual
          D pre before mid round row hstep hindex with
        ⟨record, coefficients, q, hrecord, hdecode, hsemantic, hset,
          hboundary, hvalue⟩
      have hdegree :=
        AspisR1PublicPreparation.RawSemanticPolynomialDegree28.exactPolynomial_natDegree_le_27
          coefficients
      exact .cons hstep
        ⟨record, coefficients, q, hrecord, hdecode, hsemantic, hset,
          hboundary, hvalue, hdegree⟩
        (ih (by
          intro e he
          exact hevents e (List.mem_cons_of_mem _ he)))

/-- A successful call to the real ten-round routine yields the initial decode,
ordered actual semantic calls whose challenges equal the returned alpha array,
and ten polynomial equations each tied to that step's successful decoder. -/
theorem rounds_success_actual_enriched {H : Type}
    (D : AspisR1PublicPreparation.aspis_core.Digest32 H)
    (pre : AspisR1PublicPreparation.r1_wire.Prefix)
    (self afterRounds : AspisR1PublicPreparation.r1_wire.SemanticTranscript H)
    (running : MainQM)
    (alpha : Array MainQM 10#usize)
    (hrounds : AspisR1PublicPreparation.RoundModel.rounds
      actualRoundBoundaries D pre self = .ok (.Ok (running, alpha, afterRounds))) :
    ∃ record decoded initial qs,
      AspisR1PublicPreparation.r1_wire.Prefix.validated_record pre 14#u8 =
        .ok (.Ok record) ∧
      AspisR1PublicPreparation.RawActualDecodeKMainAdapter.decodeMain
        1#usize record 0#usize = .ok (.Ok decoded) ∧
      Array.index_usize decoded 0#usize = .ok initial ∧
      AspisR1PublicPreparation.BeginCalls.SemanticRun D pre
        AspisR1PublicPreparation.RoundCalls.rows self afterRounds qs ∧
      qs = alpha.val ∧
      Run D pre AspisR1PublicPreparation.SemanticRoundsCheckedTrace.schedule
        (initial, Array.repeat 10#usize AspisR1PublicPreparation.aspis_core.field.QM31.ZERO, self)
        (running, alpha, afterRounds) := by
  obtain ⟨record, decoded, initial, hrecord, hdecode, hinitial, hrun⟩ :=
    AspisR1PublicPreparation.SemanticRoundsCheckedTrace.rounds_checked_success
      actualRoundBoundaries D pre self afterRounds running alpha hrounds
  obtain ⟨qs, hsemanticRun, hqs⟩ :=
    AspisR1PublicPreparation.RoundCalls.rounds_success actualRoundBoundaries D pre self
      afterRounds running alpha hrounds
  refine ⟨record, decoded, initial, qs, hrecord, hdecode, hinitial,
    hsemanticRun, hqs, ?_⟩
  exact checkedRun_to_run D pre _ _ _ hrun (by
    intro e he
    exact he)

#print axioms checkedRun_to_run
#print axioms rounds_success_actual_enriched
end AspisR1PublicPreparation.RawActualEnrichedSemanticRun
