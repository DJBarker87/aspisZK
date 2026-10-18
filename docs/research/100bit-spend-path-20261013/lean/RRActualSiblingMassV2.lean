import RRActualFixedParentConvolutionV7
import RRSiblingMultiplicityMassV2

open Polynomial
noncomputable section
namespace RRActualSiblingMass
variable {K : Type*} [Field K]
local instance : DecidableEq K := Classical.decEq K

noncomputable def selectedChildIndex
    (g : Nat → K[X]) (a : K) (p : K[X]) (M : Nat)
    (hp : p ≠ 0) (hzero : g 0 = p) : Nat :=
  Classical.choose (RRActualBivariateTaylorBridge.exists_actual_fixed_parent_first_nonzero_slice
    g a p M hp hzero)

noncomputable def selectedChildSlice
    (g : Nat → K[X]) (a : K) (p : K[X]) (M : Nat)
    (hp : p ≠ 0) (hzero : g 0 = p) : K[X] :=
  RRActualBivariateTaylorBridge.fixedParentCoeffSlice g a M
    (selectedChildIndex g a p M hp hzero)

theorem selectedChildSlice_degree_le_rootMultiplicity
    (g : Nat → K[X]) (a : K) (p : K[X]) (M : Nat)
    (hp : p ≠ 0) (hzero : g 0 = p) :
    (selectedChildSlice g a p M hp hzero).natDegree ≤ p.rootMultiplicity a := by
  unfold selectedChildSlice selectedChildIndex
  exact (Classical.choose_spec
    (RRActualBivariateTaylorBridge.exists_actual_fixed_parent_first_nonzero_slice
      g a p M hp hzero)).2.2.2

theorem sum_selected_child_degrees_le_parent_degree
    (g : Nat → K[X]) (p : K[X]) (M : Nat)
    (hp : p ≠ 0) (hzero : g 0 = p) :
    (∑ a ∈ p.roots.toFinset,
      (selectedChildSlice g a p M hp hzero).natDegree) ≤ p.natDegree := by
  classical
  calc
    (∑ a ∈ p.roots.toFinset,
      (selectedChildSlice g a p M hp hzero).natDegree) ≤
      ∑ a ∈ p.roots.toFinset, p.rootMultiplicity a := by
        apply Finset.sum_le_sum
        intro a ha
        exact selectedChildSlice_degree_le_rootMultiplicity g a p M hp hzero
    _ ≤ p.natDegree :=
      RRSiblingMultiplicityMass.sum_rootMultiplicity_over_roots_le_natDegree p

#print axioms sum_selected_child_degrees_le_parent_degree
end RRActualSiblingMass
