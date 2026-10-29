import PV_B3P_PreweightedStep12227
import PV_B3P_InclusiveLoop12227
namespace PV_B3P_Binding12227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding11227
set_option autoImplicit false

theorem preweighted_loop_binding12 {N : Usize}
    (packed : Array aspis_core.field.QM31 24#usize) (start : Usize)
    (values : Array aspis_core.field.QM31 N) (last group : Usize) :
    reference_terminal.add_preweighted_loop packed start values last group =
      loop (inclusive_body12 (preweighted_source_step12 start values) last) (packed,group) := by
  unfold reference_terminal.add_preweighted_loop
  apply congrArg (fun body => loop body (packed,group))
  funext state
  exact preweighted_step_binding12 start values last state.1 state.2

def source_preweighted12 {N : Usize} (packed : Array aspis_core.field.QM31 24#usize)
    (start : Usize) (values : Array aspis_core.field.QM31 N) :
    Result (Array aspis_core.field.QM31 24#usize) := do
  let first ← start / 4#usize
  let stop ← lift (Usize.wrapping_add start N)
  let before ← lift (Usize.wrapping_sub stop 1#usize)
  let last ← before / 4#usize
  loop (inclusive_body12 (preweighted_source_step12 start values) last) (packed,first)

theorem preweighted_operation_binding12 :
    @reference_terminal.add_preweighted = @source_preweighted12 := by
  funext N packed start values
  unfold reference_terminal.add_preweighted source_preweighted12
  simp only [preweighted_loop_binding12]

#print axioms preweighted_loop_binding12
#print axioms preweighted_operation_binding12
end PV_B3P_Binding12227
