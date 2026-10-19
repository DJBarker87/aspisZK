import RawActualSemanticRoundCanonicality
import RawSemanticCheckedRunSumcheck

set_option autoImplicit false
namespace AspisR1PublicPreparation.RawActualSemanticRunCanonicality

open Aeneas Aeneas.Std Result

abbrev Outcome := AspisR1PublicPreparation.SemanticRoundsCheckedTrace.Outcome

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

theorem checkedRun_actual_to_sumcheckRun {H : Type}
    (D : AspisR1PublicPreparation.aspis_core.Digest32 H)
    (pre : AspisR1PublicPreparation.r1_wire.Prefix)
    (events : List (Usize × U8)) (initial final : Outcome H)
    (hrun : AspisR1PublicPreparation.SemanticRoundsCheckedTrace.CheckedRun
      AspisR1PublicPreparation.RawActualSemanticRoundCanonicality.actualRoundBoundaries
      D pre events initial final)
    (hevents : ∀ e ∈ events,
      e ∈ AspisR1PublicPreparation.SemanticRoundsCheckedTrace.schedule) :
    AspisR1PublicPreparation.RawSemanticCheckedRunSumcheck.PolynomialSumcheckRun
      D pre events initial final := by
  induction hrun with
  | nil out => exact .nil out
  | @cons round row rest before mid after hstep htail ih =>
      have hsched := hevents (round, row) (by simp)
      have hround := schedule_round_lt_ten hsched
      have hindex : ∀ q : AspisR1PublicPreparation.RawGeneratedSemanticRoundPolynomialAdapter.MainQM,
          Array.index_usize (before.2.1.set round q) round = .ok q := by
        intro q
        unfold Array.index_usize
        simp [Array.set, hround]
      rcases AspisR1PublicPreparation.RawActualSemanticRoundCanonicality.checkedStep_polynomial_equations_actual
          D pre before mid round row hstep hindex with
        ⟨record, coefficients, q, hrecord, hdecode, hsemantic, hset, hboundary, hvalue⟩
      have hdegree :=
        AspisR1PublicPreparation.RawSemanticPolynomialDegree28.exactPolynomial_natDegree_le_27
          coefficients
      exact .cons
        ⟨record, coefficients, q, hrecord, hsemantic, hset, hboundary, hvalue, hdegree⟩
        (ih (by
          intro e he
          exact hevents e (List.mem_cons_of_mem _ he)))

/-- The concrete ten-round trace from the extracted rounds call produces the
usual ten-polynomial sumcheck record. The first polynomial endpoint remains
linked to the decoded initial running claim; a separate source bridge is still
needed to identify that claim with `maskSum`. -/
theorem checkedRun_schedule_actual_to_sumcheckRun {H : Type}
    (D : AspisR1PublicPreparation.aspis_core.Digest32 H)
    (pre : AspisR1PublicPreparation.r1_wire.Prefix)
    (initial final : Outcome H)
    (hrun : AspisR1PublicPreparation.SemanticRoundsCheckedTrace.CheckedRun
      AspisR1PublicPreparation.RawActualSemanticRoundCanonicality.actualRoundBoundaries
      D pre AspisR1PublicPreparation.SemanticRoundsCheckedTrace.schedule initial final) :
    AspisR1PublicPreparation.RawSemanticCheckedRunSumcheck.PolynomialSumcheckRun
      D pre AspisR1PublicPreparation.SemanticRoundsCheckedTrace.schedule initial final := by
  apply checkedRun_actual_to_sumcheckRun D pre _ initial final hrun
  intro e he
  exact he

/-- A successful call to the actual generated ten-round routine carries the
per-round polynomials and their endpoint/challenge recurrence equations. The
initial endpoint is the decoded row-14 claim; identifying it with `maskSum`
remains an explicit source-level boundary. -/
theorem rounds_success_actual_to_sumcheckRun {H : Type}
    (D : AspisR1PublicPreparation.aspis_core.Digest32 H)
    (pre : AspisR1PublicPreparation.r1_wire.Prefix)
    (self afterRounds : AspisR1PublicPreparation.r1_wire.SemanticTranscript H)
    (running : AspisR1PublicPreparation.RawGeneratedSemanticRoundPolynomialAdapter.MainQM)
    (alpha : Array AspisR1PublicPreparation.RawGeneratedSemanticRoundPolynomialAdapter.MainQM 10#usize)
    (hrounds : AspisR1PublicPreparation.RoundModel.rounds
      AspisR1PublicPreparation.RawActualSemanticRoundCanonicality.actualRoundBoundaries
      D pre self = .ok (.Ok (running, alpha, afterRounds))) :
    ∃ record decoded initial,
      AspisR1PublicPreparation.r1_wire.Prefix.validated_record pre 14#u8 = .ok (.Ok record) ∧
      AspisR1PublicPreparation.RawActualDecodeKMainAdapter.decodeMain
        1#usize record 0#usize = .ok (.Ok decoded) ∧
      Array.index_usize decoded 0#usize = .ok initial ∧
      AspisR1PublicPreparation.RawSemanticCheckedRunSumcheck.PolynomialSumcheckRun
        D pre AspisR1PublicPreparation.SemanticRoundsCheckedTrace.schedule
        (initial, Array.repeat 10#usize
          AspisR1PublicPreparation.aspis_core.field.QM31.ZERO, self)
        (running, alpha, afterRounds) := by
  obtain ⟨record, decoded, initial, hrecord, hdecode, hinitial, hrun⟩ :=
    AspisR1PublicPreparation.SemanticRoundsCheckedTrace.rounds_checked_success
      AspisR1PublicPreparation.RawActualSemanticRoundCanonicality.actualRoundBoundaries
      D pre self afterRounds running alpha hrounds
  exact ⟨record, decoded, initial, hrecord, hdecode, hinitial,
    checkedRun_schedule_actual_to_sumcheckRun D pre
      (initial, Array.repeat 10#usize
        AspisR1PublicPreparation.aspis_core.field.QM31.ZERO, self)
      (running, alpha, afterRounds) hrun⟩

#print axioms rounds_success_actual_to_sumcheckRun

#print axioms checkedRun_schedule_actual_to_sumcheckRun
end AspisR1PublicPreparation.RawActualSemanticRunCanonicality
