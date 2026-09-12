/-
FIRST ATTEMPT — NOT COMPILED IN THE AUTHORING ENVIRONMENT.
No declaration in this file is a certification of Aspis or a source-refinement
claim unless its concrete producer and dependency chain are separately checked.
See docs/OBLIGATIONS.md and the per-module status manifest.
-/

import Mathlib
set_option autoImplicit false
open scoped BigOperators
namespace AspisV8Completion.DistinctPair
noncomputable section
variable {A : Type*} [DecidableEq A]

/-- Cardinality of ordered DISTINCT pairs, including empty/singleton cases. -/
theorem offDiag_card (S : Finset A) : S.offDiag.card = S.card * (S.card-1) := by
  simpa using Finset.offDiag_card S

/-- Concrete finite-sum domination. The second atom bound must hold at
EVERY reachable terminal history of the first sampler, not just marginally. -/
theorem ordered_pair_mass_bound (S : Finset A)
    (joint : A → A → ℚ) (b : ℚ)
    (cell : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → joint x y ≤ b) :
    (∑ xy ∈ S.offDiag, joint xy.1 xy.2) ≤
      (S.card * (S.card-1) : Nat) * b := by
  have each : (∑ xy ∈ S.offDiag, joint xy.1 xy.2) ≤ ∑ _xy ∈ S.offDiag, b := by
    apply Finset.sum_le_sum
    intro xy member
    obtain ⟨hx,hy,hne⟩ := Finset.mem_offDiag.mp member
    exact cell xy.1 hx xy.2 hy hne
  calc
    _ ≤ ∑ _xy ∈ S.offDiag, b := each
    _ = (S.offDiag.card : ℚ)*b := by simp
    _ = (S.card*(S.card-1) : Nat)*b := by rw [offDiag_card]

/-- Algebra for the per-pair atom after two sequential uniform distinct draws. -/
theorem two_atom_product (N : ℚ) (hN : 1 < N) :
    (1/N)*(1/(N-1)) = 1/(N*(N-1)) := by ring

#print axioms ordered_pair_mass_bound
end
end AspisV8Completion.DistinctPair
