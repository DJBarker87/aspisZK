import AspisR1.CopyPatternPowerSource
import AspisR1.CopyPatternRegistrySource
import AspisR1.CopyPatternLiftSource

/-! Exact sealed indexed-candidate source partition. -/
set_option autoImplicit false
namespace AspisR1CopyPatternCandidate
open Aeneas Aeneas.Std Result Error
open AspisR1SelectedMaskProbe

@[rust_loop]
def pool_v1.pair_forest_copy_terminal.pattern_values_literal_loop1_loop0
  (openings : Array field.QM31 16#usize) (powers : Array field.QM31 16#usize)
  (limb : Std.Usize)
  (pattern : pool_v1.pair_forest_copy_terminal.CompiledPoolV1PairForestPattern)
  (value : field.QM31) :
  Result (Std.Usize × field.QM31)
  := do
  if limb < poseidon2.POSEIDON2_WIDTH
  then
    let i ← Array.index_usize pattern.kinds limb
    let value1 ←
      if i = 1#u8
      then
        do
        let i1 ← Array.index_usize pattern.columns limb
        let i2 ← lift (core.convert.num.FromUsizeU8.from i1)
        let q ← Array.index_usize openings i2
        let i3 ← Array.index_usize pattern.offsets limb
        let q1 ← pool_v1.pair_forest_copy_terminal.lift_m31 i3
        let source ← field.QM31.add q q1
        let q2 ← Array.index_usize powers limb
        let q3 ← field.QM31.mul q2 source
        field.QM31.add value q3
      else ok value
    let limb1 ← limb + 1#usize
    pool_v1.pair_forest_copy_terminal.pattern_values_literal_loop1_loop0
      openings powers limb1 pattern value1
  else ok (limb, value)
partial_fixpoint

end AspisR1CopyPatternCandidate
