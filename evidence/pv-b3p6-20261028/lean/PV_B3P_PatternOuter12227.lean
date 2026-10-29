import PV_B3P_PatternLoop12227
namespace PV_B3P_Binding12227
open Aeneas Aeneas.Std PV_B3P_227 Result ControlFlow
set_option autoImplicit false

abbrev PatternResult12 := Array aspis_core.field.QM31 14#usize
def source_pattern_outer_body12
    (openings powers : Array aspis_core.field.QM31 16#usize)
    (state : Usize × PatternResult12 × Usize) :
    Result (ControlFlow (Usize × PatternResult12 × Usize) PatternResult12) :=
  if state.2.2 < reference_copy_terminal.POOL_V1_PAIR_FOREST_COPY_TERMINAL_PATTERNS_V1 then do
    let pattern ← Array.index_usize reference_copy_terminal.constants.COPY_PATTERNS state.2.2
    let (limb,value) ← source_pattern_loop12 openings powers 0#usize pattern aspis_core.field.QM31.ZERO
    let result ← Array.update state.2.1 state.2.2 value
    let next ← lift (Usize.wrapping_add state.2.2 1#usize)
    .ok (.cont (limb,result,next))
  else .ok (.done state.2.1)

theorem pattern_outer_body_binding12
    (openings powers : Array aspis_core.field.QM31 16#usize) (limb : Usize)
    (result : PatternResult12) (index : Usize) :
    reference_copy_terminal.pattern_values_literal_loop1.body openings powers limb result index =
      source_pattern_outer_body12 openings powers (limb,result,index) := by
  simp only [reference_copy_terminal.pattern_values_literal_loop1.body,
    source_pattern_outer_body12,pattern_loop_binding12]

def source_pattern_outer12 (openings powers : Array aspis_core.field.QM31 16#usize)
    (limb : Usize) (result : PatternResult12) (index : Usize) : Result PatternResult12 :=
  loop (source_pattern_outer_body12 openings powers) (limb,result,index)

theorem pattern_outer_binding12
    (openings powers : Array aspis_core.field.QM31 16#usize) (limb : Usize)
    (result : PatternResult12) (index : Usize) :
    reference_copy_terminal.pattern_values_literal_loop1 openings powers limb result index =
      source_pattern_outer12 openings powers limb result index := by
  unfold reference_copy_terminal.pattern_values_literal_loop1 source_pattern_outer12
  apply congrArg (fun body => loop body (limb,result,index))
  funext state
  exact pattern_outer_body_binding12 openings powers state.1 state.2.1 state.2.2

#print axioms pattern_outer_body_binding12
#print axioms pattern_outer_binding12
end PV_B3P_Binding12227
