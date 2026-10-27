import PV_B3_CanonicalMul
set_option autoImplicit false
namespace PV_B3_Canonical
open Aeneas Aeneas.Std Result PV_B3_Copy_117
 theorem current_cscale (x : aspis_core.field.CM31) (s : U32) :
    ∃ z, PV_B3_Copy_117.aspis_core.field.CM31.mul_m31 x s = .ok z ∧ C z := by
  obtain ⟨a,ha,hca⟩ := current_mul x.a s
  obtain ⟨b,hb,hcb⟩ := current_mul x.b s
  refine ⟨⟨a,b⟩,?_,hca,hcb⟩
  simp only [PV_B3_Copy_117.aspis_core.field.CM31.mul_m31,ha,hb,bind_tc_ok]
#print axioms current_cscale
end PV_B3_Canonical
