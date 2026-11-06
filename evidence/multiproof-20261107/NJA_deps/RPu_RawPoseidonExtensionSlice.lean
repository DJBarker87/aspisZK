-- Exact named declaration slice from terminal extraction G.
import AspisR1SelectedMaskProbe.Funs
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
namespace AspisR1SelectedMaskProbe

/-- [aspis_r1_mask_extraction_probe::field::{aspis_r1_mask_extraction_probe::field::M31}::reduce_u62]:
    Source: 'src/field.rs', lines 145:4-148:5
    Visibility: public -/
def field.M31.reduce_u62 (value : Std.U64) : Result field.M31 := do
  let i ← field.reduce_u64 value
  ok i

/-- [aspis_r1_mask_extraction_probe::state_only_poseidon::extension_from_raw_limbs]:
    Source: 'src/statement/state_only_poseidon.rs', lines 135:0-140:1 -/
def state_only_poseidon.extension_from_raw_limbs
  (limbs : Array Std.U64 4#usize) : Result field.QM31 := do
  let i ← Array.index_usize limbs 0#usize
  let m ← field.M31.reduce_u62 i
  let i1 ← Array.index_usize limbs 1#usize
  let m1 ← field.M31.reduce_u62 i1
  let c ← field.CM31.new m m1
  let i2 ← Array.index_usize limbs 2#usize
  let m2 ← field.M31.reduce_u62 i2
  let i3 ← Array.index_usize limbs 3#usize
  let m3 ← field.M31.reduce_u62 i3
  let c1 ← field.CM31.new m2 m3
  ok { c0 := c, c1 }

/-- [aspis_r1_mask_extraction_probe::state_only_poseidon::extension_limbs]:
    Source: 'src/statement/state_only_poseidon.rs', lines 130:0-132:1 -/
def state_only_poseidon.extension_limbs
  (value : field.QM31) : Result (Array Std.U32 4#usize) := do
  let i := value.c0.a
  let i1 := value.c0.b
  let i2 := value.c1.a
  let i3 := value.c1.b
  ok (Array.make 4#usize [ i, i1, i2, i3 ])


end AspisR1SelectedMaskProbe
