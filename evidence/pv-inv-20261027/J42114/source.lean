import Mathlib.Algebra.Field.Basic
import Mathlib.Tactic.Ring
set_option autoImplicit false
namespace R1Z.PV_Inv_Circle
variable {K : Type} [Field K]

theorem denominator_factor (t i : K) (hi : i^2 = -1) :
    1+t^2=(t-i)*(t+i) := by
  calc 1+t^2 = t^2-i^2 := by rw [hi]; ring
       _ = (t-i)*(t+i) := by ring

theorem singular_iff (t i : K) (hi : i^2 = -1) :
    1+t^2=0 ↔ t=i ∨ t= -i := by
  rw [denominator_factor t i hi,mul_eq_zero,sub_eq_zero,add_eq_zero_iff_eq_neg]

theorem denominator_nonzero (t i : K) (hi : i^2 = -1)
    (hp : t ≠ i) (hm : t ≠ -i) : 1+t^2 ≠ 0 := by
  intro h
  exact ((singular_iff t i hi).mp h).elim hp hm

#print axioms denominator_factor
#print axioms singular_iff
#print axioms denominator_nonzero
end R1Z.PV_Inv_Circle
