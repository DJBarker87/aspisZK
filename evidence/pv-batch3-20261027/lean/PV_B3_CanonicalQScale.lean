import PV_B3_CanonicalCScale
set_option autoImplicit false
namespace PV_B3_Canonical
open Aeneas Aeneas.Std Result PV_B3_Copy_117
 theorem current_qscale (x : aspis_core.field.QM31) (s : U32) :
    ∃ z, PV_B3_Copy_117.aspis_core.field.QM31.mul_m31 x s = .ok z ∧ Q z := by
  obtain ⟨a,ha,hca⟩ := current_cscale x.c0 s
  obtain ⟨b,hb,hcb⟩ := current_cscale x.c1 s
  refine ⟨⟨a,b⟩,?_,hca,hcb⟩
  simp only [PV_B3_Copy_117.aspis_core.field.QM31.mul_m31,ha,hb,bind_tc_ok]
#print axioms current_qscale
end PV_B3_Canonical
