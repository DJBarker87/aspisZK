import R1Z.PV_Canon_CScale
set_option autoImplicit false
namespace R1Z.PV_Canon
open Aeneas Aeneas.Std Result ProverRwFull
 theorem current_qscale (x : aspis_core.field.QM31) (s : U32) :
    ∃ z, ProverRwP7CurrentFieldSource.aspis_core.field.QM31.mul_m31 x s = .ok z ∧ Q z := by
  obtain ⟨a,ha,hca⟩ := current_cscale x.c0 s
  obtain ⟨b,hb,hcb⟩ := current_cscale x.c1 s
  refine ⟨⟨a,b⟩,?_,hca,hcb⟩
  simp only [ProverRwP7CurrentFieldSource.aspis_core.field.QM31.mul_m31,ha,hb,bind_tc_ok]
#print axioms current_qscale
end R1Z.PV_Canon
