import RRRootMultiplicityTaylorV3
import RRChildSliceTaylorV4

open Polynomial
noncomputable section
namespace RRChildSliceTaylor
variable {K : Type*} [Field K]

theorem exists_child_slice_bounded_by_rootMultiplicity
    (g : Nat → K[X]) (a : K) (p : K[X]) (hp : p ≠ 0)
    (hzero : g 0 = p) :
    ∃ v, v ≤ p.rootMultiplicity a ∧ childCoeff g a v ≠ 0 ∧
      (childCoeff g a v).natDegree ≤ p.rootMultiplicity a := by
  classical
  have htop : childCoeff g a (p.rootMultiplicity a) ≠ 0 := by
    have hc := childCoeff_top_coeff g a (p.rootMultiplicity a)
    rw [hzero] at hc
    intro hz
    rw [hz] at hc
    exact (RRRootMultiplicityTaylor.taylor_coeff_ne_zero_at_rootMultiplicity p a hp) hc.symm
  have hex : ∃ n, childCoeff g a n ≠ 0 := ⟨p.rootMultiplicity a, htop⟩
  let v := Nat.find hex
  have hv : childCoeff g a v ≠ 0 := Nat.find_spec hex
  have hbound : v ≤ p.rootMultiplicity a := Nat.find_min' hex htop
  refine ⟨v, hbound, hv, ?_⟩
  exact (childCoeff_natDegree_le g a v).trans hbound

end RRChildSliceTaylor
