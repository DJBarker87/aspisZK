import RPu_FIz_Marginals
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIz_NormalizationNonvacuity
open FIv_NativeValue (K)
theorem mass {n : Nat} (positive : 0<n) :
    (∑ i : Fin n, if i.val=0 then (1 : K) else 0)=1 := by
  let z : Fin n := ⟨0,positive⟩
  rw [Finset.sum_eq_single z]
  · simp only [z,↓reduceIte]
  · intro i _ ne
    rw [if_neg]
    intro eq
    apply ne
    exact Fin.ext eq
  · simp
#print axioms mass
end AspisR1.FIz_NormalizationNonvacuity
end
