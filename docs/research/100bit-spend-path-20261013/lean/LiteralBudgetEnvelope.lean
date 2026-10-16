import R1LiteralClassifier
import R1PerAttemptEnvelope

/-! The actual literal classifier's 33 row budgets fit the previously checked
100-bit per-attempt envelope. These are scalar inequalities; no generated
recurrence or finite-field enumeration is evaluated. -/
set_option autoImplicit false
namespace AspisR1.LiteralBudgetEnvelope

private theorem circle_le : LiteralCircleDensity.budget ≤ PerAttemptEnvelope.B := by
  have h := PerAttemptEnvelope.semantic_row_le ⟨3, by decide⟩
  rw [SemanticBudget.budget_eq] at h
  have ha : 0 ≤ SemanticBudget.atom := by
    unfold SemanticBudget.atom R0P.SemSource.deltaQ
    positivity
  have he : LiteralCircleDensity.budget = SemanticBudget.atom := by
    rfl
  rw [he]
  norm_num [SemanticBudget.roots] at h
  linarith

private theorem opening_le :
    LiteralOpeningDensity.gammaBudget ≤ PerAttemptEnvelope.B ∧
    LiteralOpeningDensity.kappaBudget ≤ PerAttemptEnvelope.B ∧
    LiteralOpeningDensity.foldBudget ≤ PerAttemptEnvelope.B := by
  have he : OpeningSamplerBound.openingCap = LiteralOpeningDensity.gammaBudget +
      LiteralOpeningDensity.kappaBudget + 2 * LiteralOpeningDensity.foldBudget := by
    unfold OpeningSamplerBound.openingCap LiteralOpeningDensity.gammaBudget
      LiteralOpeningDensity.kappaBudget LiteralOpeningDensity.foldBudget
    ring
  have hg := LiteralOpeningDensity.gammaBudget_nonneg
  have hk := LiteralOpeningDensity.kappaBudget_nonneg
  have hf := LiteralOpeningDensity.foldBudget_nonneg
  have hc := PerAttemptEnvelope.opening_cap_le
  rw [he] at hc
  constructor
  · linarith
  constructor <;> linarith

theorem row_le (i : Nat) (hi : i < 33) :
    LiteralClassifier.budget i ≤ PerAttemptEnvelope.B := by
  by_cases hs : i < 25
  · simpa only [LiteralClassifier.budget,if_pos hs] using
      PerAttemptEnvelope.semantic_row_le ⟨i,hs⟩
  · have hc : i = 25 ∨ i = 26 ∨ i = 27 ∨ i = 28 ∨ i = 29 ∨
        i = 30 ∨ i = 31 ∨ i = 32 := by omega
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact circle_le
    · exact circle_le
    · exact opening_le.1
    · exact opening_le.2.1
    · exact opening_le.2.2
    · exact opening_le.2.2
    · exact PerAttemptEnvelope.query_cap_le
    · exact PerAttemptEnvelope.rho_cap_le

theorem thirty_three_rows_lt :
    (33 : ℚ) * PerAttemptEnvelope.B < 1 / (2^100 : ℚ) :=
  PerAttemptEnvelope.thirty_three_B_lt

#print axioms row_le
#print axioms thirty_three_rows_lt
end AspisR1.LiteralBudgetEnvelope
