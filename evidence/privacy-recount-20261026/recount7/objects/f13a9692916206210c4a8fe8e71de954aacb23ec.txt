import PV_B3_CanonicalCAdd
set_option autoImplicit false
namespace PV_B3_Canonical
open Aeneas Aeneas.Std Result PV_B3_Copy_117
 theorem current_qadd (x y : aspis_core.field.QM31) (hx : Q x) (hy : Q y) :
    ∃ z, PV_B3_Copy_117.aspis_core.field.QM31.add x y = .ok z ∧ Q z := by
  obtain ⟨a,ha,hca⟩ := current_cadd x.c0 y.c0 hx.1 hy.1
  obtain ⟨b,hb,hcb⟩ := current_cadd x.c1 y.c1 hx.2 hy.2
  refine ⟨⟨a,b⟩,?_,hca,hcb⟩
  simp only [PV_B3_Copy_117.aspis_core.field.QM31.add,ha,hb,bind_tc_ok]
#print axioms current_qadd
end PV_B3_Canonical
