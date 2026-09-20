import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-! A secant of the unit circle has nonisotropic normal in characteristic
not two. This removes a potential denominator exception from balancing
the source-shaped quotient kernel. Rust coefficient refinement is separate. -/
set_option autoImplicit false
namespace AspisV8R17
variable {F : Type*} [Field F]

theorem secant_normal_ne_zero (x0 y0 x1 y1 : F)
    (h2 : (2:F) ≠ 0) (h0 : x0^2+y0^2=1) (h1 : x1^2+y1^2=1)
    (hne : (x1,y1) ≠ (x0,y0)) :
    (y0-y1)^2+(x1-x0)^2 ≠ 0 := by
  intro hn
  have hd : (2:F)*(x0*x1+y0*y1-1)=0 := by linear_combination h0+h1-hn
  have dotOne : x0*x1+y0*y1=1 := sub_eq_zero.mp ((mul_eq_zero.mp hd).resolve_left h2)
  have identity : (x0*y1-y0*x1)^2+(x0*x1+y0*y1)^2=1 := by
    calc
      _ = (x0^2+y0^2)*(x1^2+y1^2) := by ring
      _ = 1 := by rw [h0,h1]; ring
  rw [dotOne] at identity
  have crossSq : (x0*y1-y0*x1)^2=0 := by linear_combination identity
  have crossZero : x0*y1-y0*x1=0 := sq_eq_zero_iff.mp crossSq
  have hx : x1=x0 := by linear_combination -x1*h0+x0*dotOne-y0*crossZero
  have hy : y1=y0 := by linear_combination -y1*h0+y0*dotOne+x0*crossZero
  exact hne (Prod.ext hx hy)

theorem image_balance_zero_iff (b c u v : F) (hn : b^2+c^2 ≠ 0)
    (image : b*v-c*u=0) : b*u+c*v=0 ↔ u=0 ∧ v=0 := by
  constructor
  · intro balance
    have hu : (b^2+c^2)*u=0 := by linear_combination b*balance-c*image
    have hv : (b^2+c^2)*v=0 := by linear_combination c*balance+b*image
    exact ⟨(mul_eq_zero.mp hu).resolve_left hn,(mul_eq_zero.mp hv).resolve_left hn⟩
  · rintro ⟨rfl,rfl⟩
    ring

theorem special_direction_balance (b c t : F) :
    b*(b*t)+c*(c*t)=(b^2+c^2)*t := by ring

#print axioms secant_normal_ne_zero
#print axioms image_balance_zero_iff
#print axioms special_direction_balance
end AspisV8R17
