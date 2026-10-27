import PV_B1_254_Funs
set_option autoImplicit false
namespace PV_B1_FieldCTTotal
open Aeneas Aeneas.Std Result PV_B1_254

theorem subtract_p (x : U32) : ∃ y, aspis_core.field.ct.subtract_p x=ok y := by
  simp only [aspis_core.field.ct.subtract_p,lift,bind_tc_ok]
  exact ⟨_,rfl⟩

theorem reduce64 (x : U64) : ∃ y, aspis_core.field.ct.reduce64 x=ok y := by
  unfold aspis_core.field.ct.reduce64
  simp only [lift,bind_tc_ok]
  exact subtract_p _

theorem add (a b : U32) : ∃ y, aspis_core.field.ct.add a b=ok y := by
  unfold aspis_core.field.ct.add
  simp only [lift,bind_tc_ok]
  exact subtract_p _

theorem sub (a b : U32) : ∃ y, aspis_core.field.ct.sub a b=ok y := by
  unfold aspis_core.field.ct.sub
  simp only [lift,bind_tc_ok]
  exact subtract_p _
#print axioms subtract_p
#print axioms reduce64
#print axioms add
#print axioms sub
end PV_B1_FieldCTTotal
