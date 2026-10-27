import PV_B3_CanonicalQSquare
import PV_B3_CanonicalQMul
namespace PV_B3_Canonical
open Aeneas Aeneas.Std Result PV_B3_Copy_117
set_option autoImplicit false
 theorem mask_power (x : aspis_core.field.QM31) :
    ∃ z, host_arithmetic.mask_power_26 x = ok z ∧ Q z := by
  obtain ⟨x2,h2,c2⟩ := current_qsquare x
  obtain ⟨x4,h4,c4⟩ := current_qsquare x2
  obtain ⟨x8,h8,c8⟩ := current_qsquare x4
  obtain ⟨x16,h16,c16⟩ := current_qsquare x8
  obtain ⟨q,hq,cq⟩ := current_qmul x16 x8 c16 c8
  obtain ⟨z,hz,cz⟩ := current_qmul q x2 cq c2
  refine ⟨z,?_,cz⟩
  simp only [host_arithmetic.mask_power_26,h2,h4,h8,h16,hq,hz,bind_tc_ok]
#print axioms mask_power
end PV_B3_Canonical
