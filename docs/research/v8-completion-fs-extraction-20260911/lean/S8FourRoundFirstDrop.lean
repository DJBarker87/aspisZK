import FSV8S5CompactPolynomialTarget

/-!
# Four-round ordinary residual partition

This local algebra is consumed by a terminal-checked ordinary source run.  It
does not itself assert source event inclusion: the before/after discrepancies
must still be constructed from that run.
-/
set_option autoImplicit false
set_option Elab.async false
namespace AspisV8Completion.S8FourRoundFirstDrop
open FSV8S5CompactPolynomialTarget
variable {K : Type*} [Field K] [DecidableEq K]

theorem four_round_first_drop
    (before after : Fin 4 → K)
    (initial : before 0 ≠ 0)
    (query_preserves : before 1 = after 0)
    (next2 : before 2 = after 1) (next3 : before 3 = after 2)
    (terminal : after 3 = 0) :
    ∃ j : Fin 4, before j ≠ 0 ∧ after j = 0 := by
  by_cases h0 : after 0 = 0
  · exact ⟨0, initial, h0⟩
  have b1 : before 1 ≠ 0 := by simpa only [query_preserves] using h0
  by_cases h1 : after 1 = 0
  · exact ⟨1, b1, h1⟩
  have b2 : before 2 ≠ 0 := by simpa only [next2] using h1
  by_cases h2 : after 2 = 0
  · exact ⟨2, b2, h2⟩
  have b3 : before 3 ≠ 0 := by simpa only [next3] using h2
  exact ⟨3, b3, terminal⟩

/-- A mismatched positive query update stays a separate event; otherwise some
actual round is the first nonzero-to-zero discrepancy transition. -/
theorem first_drop_or_query_discrepancy
    (before after : Fin 4 → K) (queryError : K)
    (initial : before 0 ≠ 0)
    (query_update : before 1 = after 0 + queryError)
    (next2 : before 2 = after 1) (next3 : before 3 = after 2)
    (terminal : after 3 = 0) :
    queryError ≠ 0 ∨ ∃ j : Fin 4, before j ≠ 0 ∧ after j = 0 := by
  by_cases hq : queryError = 0
  · right
    apply four_round_first_drop before after initial
    · simpa only [hq, add_zero] using query_update
    · exact next2
    · exact next3
    · exact terminal
  · exact Or.inl hq

/-- A nonzero discrepancy polynomial that vanishes at the sampled challenge
is in the already-defined degree-six root set. -/
theorem vanishing_discrepancy_is_listed
    (claimed reference : Coeff7 K) (alpha : K)
    (nonzero : poly7 (difference claimed reference) ≠ 0)
    (vanishes : (poly7 (difference claimed reference)).eval alpha = 0) :
    alpha ∈ discrepancyRoots claimed reference := by
  apply nonzero_collision_mem_discrepancyRoots claimed reference alpha nonzero
  rw [poly7_difference, Polynomial.eval_sub] at vanishes
  exact sub_eq_zero.mp vanishes

#print axioms four_round_first_drop
#print axioms first_drop_or_query_discrepancy
#print axioms vanishing_discrepancy_is_listed
end AspisV8Completion.S8FourRoundFirstDrop
