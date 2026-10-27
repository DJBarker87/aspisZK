import R1Z.PV_Canon_Carrier
import R1Z.PV_Ext_Closed_12_CM31_from_m31
set_option autoImplicit false
namespace R1Z.PV_Canon
open Aeneas Aeneas.Std Result ProverRwFull
 theorem lift_complex (x : aspis_core.field.M31) (hx : M x) :
    ∃ z, PV_Ext_IndexClosed.aspis_core.field.CM31.from_m31 x = .ok z ∧ C z := by
  refine ⟨⟨x,0#u32⟩,?_,hx,zero⟩
  simp only [PV_Ext_IndexClosed.aspis_core.field.CM31.from_m31,
    PV_Ext_IndexClosed.aspis_core.field.M31.ZERO]
#print axioms lift_complex
end R1Z.PV_Canon
