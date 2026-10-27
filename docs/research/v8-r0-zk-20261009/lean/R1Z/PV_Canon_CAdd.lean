import R1Z.PV_Canon_Add
set_option autoImplicit false
namespace R1Z.PV_Canon
open Aeneas Aeneas.Std Result ProverRwFull
 theorem current_cadd (x y : aspis_core.field.CM31) (hx : C x) (hy : C y) :
    ∃ z, ProverRwP7CurrentFieldSource.aspis_core.field.CM31.add x y = .ok z ∧ C z := by
  obtain ⟨a,ha,hca⟩ := current_add x.a y.a hx.1 hy.1
  obtain ⟨b,hb,hcb⟩ := current_add x.b y.b hx.2 hy.2
  refine ⟨⟨a,b⟩,?_,hca,hcb⟩
  simp only [ProverRwP7CurrentFieldSource.aspis_core.field.CM31.add,ha,hb,bind_tc_ok]
#print axioms current_cadd
end R1Z.PV_Canon
