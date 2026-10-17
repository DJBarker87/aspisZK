import AspisR1.CopyPatternInnerSource

/-! Exact sealed indexed-candidate source partition. -/
set_option autoImplicit false
namespace AspisR1CopyPatternCandidate
open Aeneas Aeneas.Std Result Error
open AspisR1SelectedMaskProbe

@[rust_loop]
def pool_v1.pair_forest_copy_terminal.pattern_values_literal_loop1
  (openings : Array field.QM31 16#usize) (powers : Array field.QM31 16#usize)
  (limb : Std.Usize) (result : Array field.QM31 14#usize)
  (pattern_index : Std.Usize) :
  Result (Array field.QM31 14#usize)
  := do
  if pattern_index <
    pool_v1.pair_forest_copy_terminal.POOL_V1_PAIR_FOREST_COPY_TERMINAL_PATTERNS_V1
  then
    let pattern ←
      Array.index_usize
        pool_v1.pair_forest_copy_terminal.constants.COPY_PATTERNS pattern_index
    let (limb1, value) ←
      pool_v1.pair_forest_copy_terminal.pattern_values_literal_loop1_loop0
        openings powers 0#usize pattern field.QM31.ZERO
    let a ← Array.update result pattern_index value
    let pattern_index1 ← pattern_index + 1#usize
    pool_v1.pair_forest_copy_terminal.pattern_values_literal_loop1 openings
      powers limb1 a pattern_index1
  else ok result
partial_fixpoint

end AspisR1CopyPatternCandidate
