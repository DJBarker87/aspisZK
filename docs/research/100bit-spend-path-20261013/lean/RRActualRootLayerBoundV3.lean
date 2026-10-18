import RRActualSiblingMassV2

open Polynomial
noncomputable section
namespace RRActualSiblingMass
variable {K : Type*} [Field K]
local instance : DecidableEq K := Classical.decEq K

theorem card_roots_le_sum_rootMultiplicity (p : K[X]) :
    p.roots.toFinset.card ≤ ∑ a ∈ p.roots.toFinset, p.rootMultiplicity a := by
  classical
  have hone : (∑ a ∈ p.roots.toFinset, (1 : Nat)) = p.roots.toFinset.card := by
    simp
  rw [← hone]
  apply Finset.sum_le_sum
  intro a ha
  have hpos : 0 < p.rootMultiplicity a := by
    rw [← Polynomial.count_roots]
    have haRoots : a ∈ p.roots := Multiset.mem_toFinset.mp ha
    exact Multiset.count_pos.mpr haRoots
  omega

theorem sum_selected_child_root_counts_le_parent_degree
    (g : Nat → K[X]) (p : K[X]) (M : Nat)
    (hp : p ≠ 0) (hzero : g 0 = p) :
    (∑ a ∈ p.roots.toFinset,
      (selectedChildSlice g a p M hp hzero).roots.toFinset.card) ≤ p.natDegree := by
  classical
  calc
    (∑ a ∈ p.roots.toFinset,
      (selectedChildSlice g a p M hp hzero).roots.toFinset.card) ≤
      ∑ a ∈ p.roots.toFinset,
        (selectedChildSlice g a p M hp hzero).natDegree := by
          apply Finset.sum_le_sum
          intro a ha
          exact (Multiset.toFinset_card_le _).trans
            (Polynomial.card_roots' (selectedChildSlice g a p M hp hzero))
    _ ≤ p.natDegree := sum_selected_child_degrees_le_parent_degree g p M hp hzero

#print axioms card_roots_le_sum_rootMultiplicity
#print axioms sum_selected_child_root_counts_le_parent_degree
end RRActualSiblingMass
