import R1Z.PV_Canon_Carrier
import R1Z.PV_Ext_Closed_19_QM31_from_cm31
set_option autoImplicit false
namespace R1Z.PV_Canon
open Aeneas Aeneas.Std Result ProverRwFull
 theorem lift_quartic (x : aspis_core.field.CM31) (hx : C x) :
    ∃ z, PV_Ext_IndexClosed.aspis_core.field.QM31.from_cm31 x = .ok z ∧ Q z := by
  refine ⟨⟨x,⟨0#u32,0#u32⟩⟩,?_,hx,zero,zero⟩
  simp only [PV_Ext_IndexClosed.aspis_core.field.QM31.from_cm31,
    PV_Ext_IndexClosed.aspis_core.field.CM31.ZERO,
    PV_Ext_IndexClosed.aspis_core.field.M31.ZERO]
#print axioms lift_quartic
end R1Z.PV_Canon
