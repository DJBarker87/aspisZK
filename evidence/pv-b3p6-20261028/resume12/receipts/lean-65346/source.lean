import PV_B3P_PatternOuter12227
namespace PV_B3P_Binding12227
open Aeneas Aeneas.Std PV_B3P_227 Result
set_option autoImplicit false

def source_pattern_values12 (openings : Array aspis_core.field.QM31 16#usize)
    (lambda : aspis_core.field.QM31) : Result PatternResult12 := do
  let powers := Array.repeat 16#usize aspis_core.field.QM31.ZERO
  let (powers,limb) ← reference_copy_terminal.pattern_values_literal_loop0 lambda powers lambda 0#usize
  let result := Array.repeat 14#usize aspis_core.field.QM31.ZERO
  source_pattern_outer12 openings powers limb result 0#usize

theorem pattern_values_literal_binding12 (openings : Array aspis_core.field.QM31 16#usize)
    (lambda : aspis_core.field.QM31) :
    reference_copy_terminal.pattern_values_literal openings lambda = source_pattern_values12 openings lambda := by
  unfold reference_copy_terminal.pattern_values_literal source_pattern_values12
  apply PV_B3P_Binding9227.bind_equal9
  rintro ⟨powers,limb⟩
  exact pattern_outer_binding12 openings powers limb _ 0#usize

#print axioms pattern_values_literal_binding12
end PV_B3P_Binding12227
