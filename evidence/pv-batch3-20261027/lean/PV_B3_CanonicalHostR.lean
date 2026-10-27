import PV_B3_CanonicalMulR
namespace PV_B3_Canonical
open Aeneas Aeneas.Std Result PV_B3_Copy_117
set_option autoImplicit false
 theorem host_mulr (x : aspis_core.field.CM31) (hx : C x) :
    ∃ z, host_arithmetic.cm31_mul_r x = ok z ∧ C z := by
  obtain ⟨z,hz,hc⟩ := current_mulr x hx
  refine ⟨z,?_,hc⟩
  simpa only [host_arithmetic.cm31_mul_r,aspis_core.field.CM31.new,
    aspis_core.field.mul_by_r] using hz
#print axioms host_mulr
end PV_B3_Canonical
