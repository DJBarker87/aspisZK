import R1Z.PV_Inv_Circle
import Mathlib.Tactic.FieldSimp
set_option autoImplicit false
namespace R1Z.PV_Inv_CircleImage
variable {K : Type} [Field K]

def x (t : K) := (1-t^2)/(1+t^2)
def y (t : K) := (2*t)/(1+t^2)

theorem on_circle (t : K) (hn : 1+t^2 ≠ 0) : (x t)^2+(y t)^2=1 := by
  unfold x y
  field_simp
  ring

theorem image_avoids_minus_one (t : K) (hn : 1+t^2 ≠ 0) (h2 : (2 : K) ≠ 0) : x t ≠ -1 := by
  intro he
  unfold x at he
  have h := (div_eq_iff hn).mp he
  have hzero : (2 : K)=0 := by calc 2=(1-t^2)+(1+t^2) := by ring
                                                  _=0 := by rw [h]; ring
  exact h2 hzero

#print axioms on_circle
#print axioms image_avoids_minus_one
end R1Z.PV_Inv_CircleImage
