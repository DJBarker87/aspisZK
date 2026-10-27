import PV_B3_CanonicalPrepareComponent
import PV_B3_CanonicalCAdd
set_option autoImplicit false
namespace PV_B3_Canonical
open Aeneas Aeneas.Std Result PV_B3_Copy_117
abbrev Prepared := PV_B3_Copy_117.host_arithmetic.PreparedQm31Multiplier
def PreparedCanonical (x : Prepared) : Prop := ∀ v ∈ x.components.val, Triple v
 theorem prepare_canonical (x : aspis_core.field.QM31) (hx : Q x) :
    ∃ z, PV_B3_Copy_117.host_arithmetic.PreparedQm31Multiplier.new x = .ok z ∧ PreparedCanonical z := by
  obtain ⟨a,ha,hca⟩ := prepare_component x.c0 hx.1
  obtain ⟨b,hb,hcb⟩ := prepare_component x.c1 hx.2
  obtain ⟨c,hc,hcc⟩ := current_cadd x.c0 x.c1 hx.1 hx.2
  obtain ⟨d,hd,hcd⟩ := prepare_component c hcc
  refine ⟨⟨Array.make 3#usize [a,b,d]⟩,?_,?_⟩
  · simp only [PV_B3_Copy_117.host_arithmetic.PreparedQm31Multiplier.new,
      ha,hb,hc,hd,bind_tc_ok]
  · intro v hv
    change v ∈ [a,b,d] at hv
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hv
    rcases hv with rfl | rfl | rfl
    · exact hca
    · exact hcb
    · exact hcd
#print axioms prepare_canonical
end PV_B3_Canonical
