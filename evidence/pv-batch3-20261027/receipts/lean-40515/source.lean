import PV_B3_Copy_117_Funs
import PV_B3_Result
namespace PV_B3_LinearsCounter
open Aeneas Aeneas.Std Result ControlFlow PV_B3_Result PV_B3_Copy_117
set_option autoImplicit false
abbrev Q := aspis_core.field.QM31
abbrev State := Q × Q × Usize
def Progress (i : Usize) : ControlFlow State (Q×Q) → Prop
 | .done _ => True
 | .cont s => s.2.2 = Usize.wrapping_sub i 1#usize
 theorem body_counter (point : Array Q 10#usize) (suffix weighted : Q) (i : Usize) :
    Safe (Progress i) (host_arithmetic.selected_mask_linears_loop.body point suffix weighted i) := by
  unfold host_arithmetic.selected_mask_linears_loop.body
  simp only [lift,bind_tc_ok]
  split
  · apply bind_any
    intro value
    apply bind_any
    intro suffix1
    split
    · apply bind_any
      intro weighted1
      intro cf h
      cases h
      rfl
    · intro cf h
      cases h
      rfl
  · intro cf h
    cases h
    trivial
#print axioms Progress
#print axioms body_counter
end PV_B3_LinearsCounter
