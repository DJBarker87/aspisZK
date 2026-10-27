import R1Z.PV_Canon_Double
import R1Z.PV_Canon_Sub
set_option autoImplicit false
namespace R1Z.PV_Canon
open Aeneas Aeneas.Std Result ProverRwFull
 theorem current_mulr (x : aspis_core.field.CM31) (hx : C x) :
    ∃ z, ProverRwP7CurrentFieldSource.aspis_core.field.mul_by_r x = .ok z ∧ C z := by
  obtain ⟨a,ha,hca⟩ := current_double x.a hx.1
  obtain ⟨b,hb,hcb⟩ := current_sub a x.b hca hx.2
  obtain ⟨c,hc,hcc⟩ := current_double x.b hx.2
  obtain ⟨d,hd,hcd⟩ := current_add x.a c hx.1 hcc
  refine ⟨⟨b,d⟩,?_,hcb,hcd⟩
  simp only [ProverRwP7CurrentFieldSource.aspis_core.field.mul_by_r,ha,hb,hc,hd,bind_tc_ok]
#print axioms current_mulr
end R1Z.PV_Canon
