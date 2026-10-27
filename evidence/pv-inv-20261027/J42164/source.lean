import R1Z.PV_Inv_CircleImage
set_option autoImplicit false
namespace R1Z.PV_Inv_CircleRecovery
open PV_Inv_CircleImage
variable {K : Type} [Field K]

theorem one_add_x (t : K) (hn : 1+t^2 ≠ 0) : 1+x t=2/(1+t^2) := by
  unfold x
  field_simp
  ring

theorem inverse_parameter (t : K) (hn : 1+t^2 ≠ 0) (h2 : (2 : K) ≠ 0) :
    y t/(1+x t)=t := by
  rw [one_add_x t hn]
  unfold y
  field_simp

theorem rational_injective (s t : K) (hs : 1+s^2 ≠ 0) (ht : 1+t^2 ≠ 0)
    (h2 : (2 : K) ≠ 0) (hx : x s=x t) (hy : y s=y t) : s=t := by
  rw [←inverse_parameter s hs h2,←inverse_parameter t ht h2,hx,hy]

#print axioms one_add_x
#print axioms inverse_parameter
#print axioms rational_injective
end R1Z.PV_Inv_CircleRecovery
