import R1Z.PV_Canon_Mul
set_option autoImplicit false
namespace R1Z.PV_Canon
open Aeneas Aeneas.Std Result ProverRwFull
 theorem current_cscale (x : aspis_core.field.CM31) (s : U32) :
    ∃ z, ProverRwP7CurrentFieldSource.aspis_core.field.CM31.mul_m31 x s = .ok z ∧ C z := by
  obtain ⟨a,ha,hca⟩ := current_mul x.a s
  obtain ⟨b,hb,hcb⟩ := current_mul x.b s
  refine ⟨⟨a,b⟩,?_,hca,hcb⟩
  simp only [ProverRwP7CurrentFieldSource.aspis_core.field.CM31.mul_m31,ha,hb,bind_tc_ok]
#print axioms current_cscale
end R1Z.PV_Canon
