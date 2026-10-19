import R0C.SlackObstruction

/-! Exact rational ledger for the conditional five-round theorem. This does
not assert a concrete sampler instance or an unconditional security bound. -/
set_option autoImplicit false
namespace R0C.SlackBits
open R0C.SlackStatement R0C.ConcreteSlack R0C.SlackObstruction
open AspisWideTower AspisCircleGroupOrder
noncomputable section

/-- Again only 22 factors, not a large Pascal recurrence. -/
theorem bad_query_count : Nat.choose 9557 22 = 3204816658150512709790016143025871214703406297554365823658832464480 := by
  rw [Nat.choose_eq_descFactorial_div_factorial]
  norm_num [Nat.descFactorial, Nat.factorial]

theorem row_le_query (i : Nat) (hi : i < 5) :
    R0FS.ε WideExact i ≤ R0FS.ε WideExact 4 := by
  interval_cases i <;>
    simp only [R0FS.ε, wideExact_card] <;>
    norm_num [bad_query_count, query_count, P]

/-- Reduce the five-row maximum BEFORE instantiating the concrete field. -/
theorem max_five_eq_last (e : Nat → ℚ) (hn : 0 ≤ e 4)
    (hb : ∀ i, i < 5 → e i ≤ e 4) : FS.maxErr e 5 = e 4 := by
  change max (e 0) (max (e 1) (max (e 2) (max (e 3) (max (e 4) 0)))) = _
  rw [max_eq_left hn, max_eq_right (hb 3 (by omega)),
    max_eq_right (hb 2 (by omega)), max_eq_right (hb 1 (by omega)),
    max_eq_right (hb 0 (by omega))]

theorem max_error_query : FS.maxErr (epsilonSlack WideExact delta0) 5 =
    epsilonSlack WideExact delta0 4 := by
  have hscale : 0 ≤ 1+delta0 := by linarith [delta0_nonneg]
  apply max_five_eq_last
  · apply mul_nonneg hscale
    change 0 ≤ (Nat.choose 9557 22 : ℚ) / (Nat.choose 262144 22 : ℚ)
    positivity
  · intro i hi
    exact mul_le_mul_of_nonneg_left (row_le_query i hi) hscale

theorem max_error_formula : FS.maxErr (epsilonSlack WideExact delta0) 5 =
    (257 * (P^8 : ℚ) / (256^32 : ℚ)) *
      ((Nat.choose 9557 22 : ℚ) / (Nat.choose 262144 22 : ℚ)) := by
  rw [max_error_query]
  simp only [epsilonSlack, R0FS.ε, delta0]
  ring

#print axioms bad_query_count
#print axioms row_le_query
#print axioms max_five_eq_last
#print axioms max_error_query
#print axioms max_error_formula
end
end R0C.SlackBits
