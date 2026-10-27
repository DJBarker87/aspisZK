import R1Z.PV_Canon_Add
set_option autoImplicit false
namespace R1Z.PV_Canon
open Aeneas Aeneas.Std Result ProverRwFull
abbrev PrepareComponent := ProverRwP7CurrentFieldSource.aspis_core.field.PreparedQm31Multiplier.new.closure.Insts.CoreOpsFunctionFnTupleCM31ArrayM313.call
def Triple (xs : Array U32 3#usize) : Prop := ∀ x ∈ xs.val, M x
 theorem prepare_component (x : aspis_core.field.CM31) (hx : C x) :
    ∃ z, PrepareComponent () x = .ok z ∧ Triple z := by
  obtain ⟨m,hm,hcm⟩ := current_add x.a x.b hx.1 hx.2
  refine ⟨Array.make 3#usize [x.a,x.b,m],?_,?_⟩
  · simp only [PrepareComponent,ProverRwP7CurrentFieldSource.aspis_core.field.PreparedQm31Multiplier.new.closure.Insts.CoreOpsFunctionFnTupleCM31ArrayM313.call,hm,bind_tc_ok]
  · intro v hv
    change v ∈ [x.a,x.b,m] at hv
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hv
    rcases hv with rfl | rfl | rfl
    · exact hx.1
    · exact hx.2
    · exact hcm
#print axioms prepare_component
end R1Z.PV_Canon
