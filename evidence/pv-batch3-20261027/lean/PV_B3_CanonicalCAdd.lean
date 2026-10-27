import PV_B3_CanonicalAdd
set_option autoImplicit false
namespace PV_B3_Canonical
open Aeneas Aeneas.Std Result PV_B3_Copy_117
 theorem current_cadd (x y : aspis_core.field.CM31) (hx : C x) (hy : C y) :
    ∃ z, PV_B3_Copy_117.aspis_core.field.CM31.add x y = .ok z ∧ C z := by
  obtain ⟨a,ha,hca⟩ := current_add x.a y.a hx.1 hy.1
  obtain ⟨b,hb,hcb⟩ := current_add x.b y.b hx.2 hy.2
  refine ⟨⟨a,b⟩,?_,hca,hcb⟩
  simp only [PV_B3_Copy_117.aspis_core.field.CM31.add,ha,hb,bind_tc_ok]
#print axioms current_cadd
end PV_B3_Canonical
