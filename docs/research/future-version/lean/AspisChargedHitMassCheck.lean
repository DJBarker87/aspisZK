import AspisChargedHitMass

/-! Check of the per-step generalisation against R1 (not a change to R1).

The weighted bound `Q · capMax + verifierCharge` of
`AspisPerStep.ChargedHitMass.restricted_union_bound_weighted` is pointwise at
most R1's `(Q + 34) · B`, and R1's
`Frozen2StartChargeProbability.restricted_union_bound` (same hypotheses, same
conclusion) is re-derived from it. This re-derivation checks the
generalisation; it neither tightens nor replaces R1's theorem.

The domination is proved symbolically from the per-class facts
(`classCap_le_B`, `LiteralBudgetEnvelope.row_le`,
`PerAttemptEnvelope.opening_cap_le`) and the 33-term list structure; no
budget numeral is evaluated. -/
set_option autoImplicit false
noncomputable section
namespace AspisPerStep.ChargedHitMassCheck
open FS FS2 R0C.V3
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.CausalFirstHitUnionBound
open AspisR1 OraclePortStoredExperimentC4 OraclePortFrozen2Consumer
open RawRecordedOracleExtractionMassBin Frozen2StartChargePrefix Frozen2StartChargeClean
open AspisPerStep.RowCharge AspisPerStep.RowStarts AspisPerStep.ChargedHitMass

theorem capMax_le_B : capMax ≤ PerAttemptEnvelope.B := by
  unfold capMax
  refine max_le (LiteralBudgetEnvelope.row_le 0 (by omega)) (max_le
    (LiteralBudgetEnvelope.row_le 1 (by omega)) (max_le
    (LiteralBudgetEnvelope.row_le 26 (by omega)) (max_le
    PerAttemptEnvelope.opening_cap_le (max_le
    (LiteralBudgetEnvelope.row_le 31 (by omega))
    (LiteralBudgetEnvelope.row_le 32 (by omega))))))

theorem classCaps_sum_le : ((List.range 33).map classCap).sum ≤ 33 * PerAttemptEnvelope.B := by
  have h := List.sum_le_card_nsmul ((List.range 33).map classCap) PerAttemptEnvelope.B
    (by
      intro x hx
      obtain ⟨n, _, rfl⟩ := List.mem_map.mp hx
      exact classCap_le_B n)
  rw [List.length_map, List.length_range, nsmul_eq_mul] at h
  exact_mod_cast h

theorem verifierCharge_le : verifierCharge ≤ 34 * PerAttemptEnvelope.B := by
  rw [verifierCharge_eq]
  have h1 := classCaps_sum_le
  have h2 := capMax_le_B
  linarith

/-- Pointwise domination of the weighted bound by R1's form. -/
theorem weighted_le_uniform (Q : Nat) :
    (Q : ℚ) * capMax + verifierCharge ≤ ((Q + 34 : Nat) : ℚ) * PerAttemptEnvelope.B := by
  have hQ : (0 : ℚ) ≤ Q := Nat.cast_nonneg Q
  have h1 : (Q : ℚ) * capMax ≤ (Q : ℚ) * PerAttemptEnvelope.B :=
    mul_le_mul_of_nonneg_left capMax_le_B hQ
  have h2 := verifierCharge_le
  push_cast
  linarith

/-- R1's `Frozen2StartChargeProbability.restricted_union_bound`, same
hypotheses and conclusion, re-derived from the weighted theorem. -/
theorem restricted_union_bound_via_weighted (D : LiteralByteProtocol.Decoder) (P : Prover)
    (Q : Nat) (hq : ∀ H : Bytes → State, (eval H P).1.length ≤ Q) :
    lazyMean (projected D P) emptyTable (fun run => indicator (prefixHit D P run)) ≤
      ((Q + 34 : Nat) : ℚ) * PerAttemptEnvelope.B :=
  (restricted_union_bound_weighted D P Q hq).trans (weighted_le_uniform Q)

#print axioms capMax_le_B
#print axioms verifierCharge_le
#print axioms weighted_le_uniform
#print axioms restricted_union_bound_via_weighted
end AspisPerStep.ChargedHitMassCheck
end
