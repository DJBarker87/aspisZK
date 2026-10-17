import AspisR1.CopyPatternOuterSource

/-! Exact sealed indexed-candidate source partition. -/
set_option autoImplicit false
namespace AspisR1CopyPatternCandidate
open Aeneas Aeneas.Std Result Error
open AspisR1SelectedMaskProbe

def pool_v1.pair_forest_copy_terminal.pattern_values_literal
  (openings : Array field.QM31 16#usize) (lambda : field.QM31) :
  Result (Array field.QM31 14#usize)
  := do
  let powers := Array.repeat 16#usize field.QM31.ZERO
  let (powers1, limb) ←
    pool_v1.pair_forest_copy_terminal.pattern_values_literal_loop0 lambda
      powers lambda 0#usize
  let result := Array.repeat 14#usize field.QM31.ZERO
  pool_v1.pair_forest_copy_terminal.pattern_values_literal_loop1 openings
    powers1 limb result 0#usize

def pool_v1.pair_forest_copy_terminal.pattern_values
  (openings : Array field.QM31 16#usize) (lambda : field.QM31) :
  Result (Array field.QM31 14#usize)
  := do
  pool_v1.pair_forest_copy_terminal.pattern_values_literal openings lambda

end AspisR1CopyPatternCandidate
