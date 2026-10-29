import R1Z.CommitReadsR1

/-! Arithmetic joins of the actual commitment-budget predicates. These facts
reduce redundant premises; they do not identify a universal source read log. -/
set_option autoImplicit false
namespace R1Z.ProverCommitBudgetJoin
open R1Z.CommitReadsR1

theorem exact_block_budget (E L : Nat) (capacity : 16 * L ≤ E * 8)
    (blocks : E ≤ 2 * L) : E = 2 * L := by omega

theorem counter_bounds (E₁ E₂ L₁ L₂ : Nat) (cells : RCommitCount L₁ L₂)
    (blocks₁ : E₁ ≤ 2 * L₁) (blocks₂ : E₂ ≤ 2 * L₂) :
    E₁ ≤ 2^64 ∧ E₂ ≤ 2^64 := by
  rcases cells with ⟨first, second⟩
  constructor <;> omega

/-- With the counts fixed, choosing the actual worst-case budgets discharges
both capacity and upper block inequalities, and their counter obligations. -/
theorem canonical_budgets (L₁ L₂ : Nat) (cells : RCommitCount L₁ L₂) :
    16 * L₁ ≤ (2 * L₁) * 8 ∧ 16 * L₂ ≤ (2 * L₂) * 8 ∧
    2 * L₁ ≤ 2^64 ∧ 2 * L₂ ≤ 2^64 := by
  have counters := counter_bounds (2*L₁) (2*L₂) L₁ L₂ cells le_rfl le_rfl
  exact ⟨by omega, by omega, counters⟩

/-- Universal counter distinctness below the budget, before any LE64 encoding.
This does not identify which blocks a particular source execution reads. -/
theorem no_counter_wrap (E L₁ L₂ : Nat) (cells : RCommitCount L₁ L₂)
    (blocks : E ≤ 2 * L₁) (i j : Fin E) :
    i.val % 2^64 = j.val % 2^64 ↔ i = j := by
  have bound := (counter_bounds E 0 L₁ L₂ cells blocks (by omega)).1
  rw [Nat.mod_eq_of_lt (lt_of_lt_of_le i.isLt bound),
    Nat.mod_eq_of_lt (lt_of_lt_of_le j.isLt bound), Fin.ext_iff]

#print axioms exact_block_budget
#print axioms counter_bounds
#print axioms canonical_budgets
#print axioms no_counter_wrap
end R1Z.ProverCommitBudgetJoin
