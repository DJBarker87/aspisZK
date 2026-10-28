import PV_B3_Copy_222_Funs
import PV_B3_Result
namespace PV_B3_EvalCounter222
open Aeneas Aeneas.Std Result ControlFlow PV_B3_Result PV_B3_Copy_222
set_option autoImplicit false
abbrev Q := aspis_core.field.QM31
abbrev State := Q × Usize

def Progress (weights : host_multilinear.SparseWeights) (i : Usize) :
    ControlFlow State Q → Prop
  | .done _ => True
  | .cont next => i.val < weights.len.val ∧ next.2 = Usize.wrapping_add i 1#usize

theorem body_counter (column : Slice Q) (weights : host_multilinear.SparseWeights)
    (sum : Q) (i : Usize) :
    Safe (Progress weights i)
      (host_multilinear.multilinear_evaluate_qm31_loop.body column weights sum i) := by
  unfold host_multilinear.multilinear_evaluate_qm31_loop.body
  simp only [lift, bind_tc_ok]
  split
  · rename_i hi
    apply bind_any
    rintro ⟨row, weight⟩
    apply bind_any
    intro q
    apply bind_any
    intro product
    apply bind_any
    intro sum1
    intro cf h
    cases h
    exact ⟨hi, rfl⟩
  · intro cf h
    cases h
    trivial

#print axioms Progress
#print axioms body_counter
end PV_B3_EvalCounter222
