import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Tactic.Ring

/-! Algebra behind the arbitrary-weight extension of the old grouped
normal/carry contraction. Actual low/carry geometry, index layout and field
source refinement remain separate; no witness or privacy premise is used. -/
set_option autoImplicit false
namespace AspisV8R17.WeightedGroups
open scoped BigOperators
variable {G B K : Type*} [Fintype G] [Fintype B] [CommRing K]

def normalSum (w : G → B → K) (normal : B → K) (r : G) : K :=
  ∑ b, w r b * normal b

def carrySum (w : G → B → K) (carry : B → K) (r : G) : K :=
  ∑ b, w r b * carry b

/-- Keep every output group, including those outside the weight support.
The carry matrix may connect a supported input row to any output row. -/
theorem contract_expand (w : G → B → K) (normal carry : B → K)
    (edge : G → G → K) (high : G → K) :
    (∑ j, high j * (normalSum w normal j + ∑ r, edge j r * carrySum w carry r)) =
      ∑ r, ∑ b, w r b * (high r * normal b + (∑ j, high j * edge j r) * carry b) := by
  simp only [normalSum, carrySum, mul_add, Finset.sum_add_distrib,
    Finset.mul_sum, Finset.sum_mul]
  congr 1
  · apply Finset.sum_congr rfl
    intro r hr
    apply Finset.sum_congr rfl
    intro b hb
    ring
  · rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro r hr
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro b hb
    apply Finset.sum_congr rfl
    intro j hj
    ring

theorem zero_row (w : G → B → K) (normal carry : B → K) (r : G)
    (hz : ∀ b, w r b = 0) : normalSum w normal r = 0 ∧ carrySum w carry r = 0 := by
  simp [normalSum, carrySum, hz]

/-- Sparse carry positions are justified by public geometry, not coefficient
values. No assumption that the arbitrary row itself is sparse is made. -/
theorem carry_support [DecidableEq B] (w : G → B → K) (carry : B → K)
    (support : Finset B) (hc : ∀ b, b ∉ support → carry b = 0) (r : G) :
    carrySum w carry r = ∑ b ∈ support, w r b * carry b := by
  unfold carrySum
  symm
  apply Finset.sum_subset (Finset.subset_univ support)
  intro b hb hn
  simp [hc b hn]

#print axioms contract_expand
#print axioms zero_row
#print axioms carry_support
end AspisV8R17.WeightedGroups
