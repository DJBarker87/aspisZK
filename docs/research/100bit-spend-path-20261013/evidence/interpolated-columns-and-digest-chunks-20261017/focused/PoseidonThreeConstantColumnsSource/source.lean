import PoseidonThreeConstantLimbV4

/-! Exact missing columns loop/wrapper from candidate Funs f1e258056294e84777f56f2a1ea3572329eca52b4bb553bfc6c58027bef1604c. -/
namespace AspisR1SelectedMaskProbe
open Aeneas Aeneas.Std Result
/-- [aspis_r1_mask_extraction_probe::state_only_poseidon::interpolate_three_constant_columns]: loop 0:
    Source: 'src/statement/state_only_poseidon.rs', lines 444:4-484:5 -/
@[rust_loop]
def state_only_poseidon.interpolate_three_constant_columns_loop
  (weights : Array field.QM31 3#usize) (column0 : Array Std.U32 16#usize)
  (column1 : Array Std.U32 16#usize) (column2 : Array Std.U32 16#usize)
  (output : Array field.QM31 16#usize) (lane : Std.Usize) :
  Result (Array field.QM31 16#usize)
  := do
  if lane < poseidon2.POSEIDON2_WIDTH
  then
    let q ← Array.index_usize weights 0#usize
    let i := q.c0.a
    let q1 ← Array.index_usize weights 1#usize
    let i1 := q1.c0.a
    let q2 ← Array.index_usize weights 2#usize
    let i2 := q2.c0.a
    let i3 ← Array.index_usize column0 lane
    let i4 ← Array.index_usize column1 lane
    let i5 ← Array.index_usize column2 lane
    let m ←
      state_only_poseidon.interpolate_three_constant_limb i i1 i2 i3 i4 i5
    let i6 := q.c0.b
    let i7 := q1.c0.b
    let i8 := q2.c0.b
    let m1 ←
      state_only_poseidon.interpolate_three_constant_limb i6 i7 i8 i3 i4 i5
    let c ← field.CM31.new m m1
    let i9 := q.c1.a
    let i10 := q1.c1.a
    let i11 := q2.c1.a
    let m2 ←
      state_only_poseidon.interpolate_three_constant_limb i9 i10 i11 i3 i4 i5
    let i12 := q.c1.b
    let i13 := q1.c1.b
    let i14 := q2.c1.b
    let m3 ←
      state_only_poseidon.interpolate_three_constant_limb i12 i13 i14 i3 i4 i5
    let c1 ← field.CM31.new m2 m3
    let a ← Array.update output lane ({ c0 := c, c1 } : field.QM31)
    let lane1 ← lane + 1#usize
    state_only_poseidon.interpolate_three_constant_columns_loop weights column0
      column1 column2 a lane1
  else ok output
partial_fixpoint

/-- [aspis_r1_mask_extraction_probe::state_only_poseidon::interpolate_three_constant_columns]:
    Source: 'src/statement/state_only_poseidon.rs', lines 436:0-486:1 -/
def state_only_poseidon.interpolate_three_constant_columns
  (weights : Array field.QM31 3#usize) (column0 : Array Std.U32 16#usize)
  (column1 : Array Std.U32 16#usize) (column2 : Array Std.U32 16#usize) :
  Result (Array field.QM31 16#usize)
  := do
  let output := Array.repeat 16#usize field.QM31.ZERO
  state_only_poseidon.interpolate_three_constant_columns_loop weights column0
    column1 column2 output 0#usize


end AspisR1SelectedMaskProbe
