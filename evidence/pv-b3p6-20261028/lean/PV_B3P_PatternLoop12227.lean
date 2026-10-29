import PV_B3P_PatternStep12227
namespace PV_B3P_Binding12227
open Aeneas Aeneas.Std PV_B3P_227 Result ControlFlow
set_option autoImplicit false

def source_pattern_body12
    (openings powers : Array aspis_core.field.QM31 16#usize)
    (pattern : reference_copy_terminal.CompiledPoolV1PairForestPattern)
    (state : Usize × aspis_core.field.QM31) :
    Result (ControlFlow (Usize × aspis_core.field.QM31) (Usize × aspis_core.field.QM31)) :=
  if state.1 < aspis_statement.poseidon2.POSEIDON2_WIDTH then do
    let value ← source_pattern_step12 pattern state.1 openings powers state.2
    let next ← lift (Usize.wrapping_add state.1 1#usize)
    .ok (.cont (next,value))
  else .ok (.done state)

theorem pattern_body_binding12
    (openings powers : Array aspis_core.field.QM31 16#usize)
    (pattern : reference_copy_terminal.CompiledPoolV1PairForestPattern)
    (limb : Usize) (value : aspis_core.field.QM31) :
    reference_copy_terminal.pattern_values_literal_loop1_loop0.body openings powers pattern limb value =
      source_pattern_body12 openings powers pattern (limb,value) := by
  simp only [reference_copy_terminal.pattern_values_literal_loop1_loop0.body,
    source_pattern_body12,pattern_step_binding12]

def source_pattern_loop12
    (openings powers : Array aspis_core.field.QM31 16#usize) (limb : Usize)
    (pattern : reference_copy_terminal.CompiledPoolV1PairForestPattern)
    (value : aspis_core.field.QM31) : Result (Usize × aspis_core.field.QM31) :=
  loop (source_pattern_body12 openings powers pattern) (limb,value)

theorem pattern_loop_binding12
    (openings powers : Array aspis_core.field.QM31 16#usize) (limb : Usize)
    (pattern : reference_copy_terminal.CompiledPoolV1PairForestPattern)
    (value : aspis_core.field.QM31) :
    reference_copy_terminal.pattern_values_literal_loop1_loop0 openings powers limb pattern value =
      source_pattern_loop12 openings powers limb pattern value := by
  unfold reference_copy_terminal.pattern_values_literal_loop1_loop0 source_pattern_loop12
  apply congrArg (fun body => loop body (limb,value))
  funext state
  exact pattern_body_binding12 openings powers pattern state.1 state.2

#print axioms pattern_body_binding12
#print axioms pattern_loop_binding12
end PV_B3P_Binding12227
