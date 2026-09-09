import Mathlib.Algebra.BigOperators.Fin

/-! Symbolic splitting of consecutive scalar powers. No concrete field or
finite-field enumeration appears in this computation. -/
set_option autoImplicit false
namespace AspisV8.ScalarPowerSplit

theorem split {F : Type*} [CommSemiring F] (m n : ℕ)
    (values : Fin (m+n) → F) (gamma : F) :
    (∑ lane : Fin (m+n), gamma^lane.val*values lane)=
      (∑ lane : Fin m, gamma^lane.val*values (Fin.castAdd n lane))+
        gamma^m*(∑ lane : Fin n, gamma^lane.val*values (Fin.natAdd m lane)) := by
  rw [Fin.sum_univ_add]
  simp only [Fin.val_castAdd,Fin.val_natAdd,pow_add,Finset.mul_sum,mul_assoc]

#print axioms split
end AspisV8.ScalarPowerSplit
