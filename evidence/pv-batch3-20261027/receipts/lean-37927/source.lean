import PV_B3_Copy_222_Funs
import PV_B3_Result
namespace PV_B3_PrefixCounter222
open Aeneas Aeneas.Std Result ControlFlow PV_B3_Result PV_B3_Copy_222
set_option autoImplicit false
abbrev Q := aspis_core.field.QM31

def Progress (i : Usize) : ControlFlow Usize Usize → Prop
  | .done _ => True
  | .cont next => 0 < i.val ∧ next = Usize.wrapping_sub i 1#usize

theorem body_counter (point : Array Q 10#usize) (i : Usize) :
    Safe (Progress i) (host_multilinear.sparse_eq_weights_loop0.body point i) := by
  unfold host_multilinear.sparse_eq_weights_loop0.body
  simp only [lift, bind_tc_ok]
  split
  · rename_i hi
    apply bind_any
    intro q
    apply bind_any
    intro b
    split
    · intro cf h
      cases h
      exact ⟨hi, rfl⟩
    · apply bind_any
      intro q1
      apply bind_any
      intro b1
      split
      · intro cf h
        cases h
        exact ⟨hi, rfl⟩
      · intro cf h
        cases h
        trivial
  · intro cf h
    cases h
    trivial

#print axioms Progress
#print axioms body_counter
end PV_B3_PrefixCounter222
