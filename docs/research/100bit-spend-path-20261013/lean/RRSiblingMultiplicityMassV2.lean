import Mathlib.Algebra.Polynomial.Roots

open Polynomial
noncomputable section
namespace RRSiblingMultiplicityMass
variable {K : Type*} [Field K]
local instance : DecidableEq K := Classical.decEq K

theorem sum_rootMultiplicity_over_roots_le_natDegree (p : K[X]) :
    (∑ a ∈ p.roots.toFinset, p.rootMultiplicity a) ≤ p.natDegree := by
  classical
  calc
    (∑ a ∈ p.roots.toFinset, p.rootMultiplicity a) = p.roots.card := by
      rw [← Multiset.sum_count_eq_card (s := p.roots.toFinset) (m := p.roots)]
      · simp
      · intro a ha
        exact Multiset.mem_toFinset.mpr ha
    _ ≤ p.natDegree := Polynomial.card_roots' p

#print axioms sum_rootMultiplicity_over_roots_le_natDegree
end RRSiblingMultiplicityMass
