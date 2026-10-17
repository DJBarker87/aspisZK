import PoseidonInternalRoundExact
import PoseidonRemainingConstantsExact

/-! Exact missing scalar-weight dot source cone from candidate Funs SHA
f1e258056294e84777f56f2a1ea3572329eca52b4bb553bfc6c58027bef1604c.
Used by interpolated_internal_pair at its seven-weight boundary. Existing
field/reducer owners are imported unchanged. -/
namespace AspisR1SelectedMaskProbe
open Aeneas Aeneas.Std Result
/-- [aspis_r1_mask_extraction_probe::field::qm31_m31_dot]: loop 0:
    Source: 'src/field.rs', lines 1456:8-1464:9
    Visibility: public -/
@[rust_loop]
def field.qm31_m31_dot_loop0
  (weights : Slice field.QM31) (values : Slice field.M31)
  (raw1 : Array Std.U64 4#usize) (index : Std.Usize) :
  Result (Array Std.U64 4#usize)
  := do
  let i := Slice.len weights
  if index < i
  then
    let weight ← Slice.index_usize weights index
    let m ← Slice.index_usize values index
    let value ← lift (core.convert.num.FromU64U32.from m)
    let i1 := weight.c0.a
    let i2 ← lift (core.convert.num.FromU64U32.from i1)
    let i3 ← i2 * value
    let i4 ← Array.index_usize raw1 0#usize
    let i5 ← i4 + i3
    let raw2 ← Array.update raw1 0#usize i5
    let i6 := weight.c0.b
    let i7 ← lift (core.convert.num.FromU64U32.from i6)
    let i8 ← i7 * value
    let i9 ← Array.index_usize raw2 1#usize
    let i10 ← i9 + i8
    let raw3 ← Array.update raw2 1#usize i10
    let i11 := weight.c1.a
    let i12 ← lift (core.convert.num.FromU64U32.from i11)
    let i13 ← i12 * value
    let i14 ← Array.index_usize raw3 2#usize
    let i15 ← i14 + i13
    let raw4 ← Array.update raw3 2#usize i15
    let i16 := weight.c1.b
    let i17 ← lift (core.convert.num.FromU64U32.from i16)
    let i18 ← i17 * value
    let i19 ← Array.index_usize raw4 3#usize
    let i20 ← i19 + i18
    let a ← Array.update raw4 3#usize i20
    let index1 ← index + 1#usize
    field.qm31_m31_dot_loop0 weights values a index1
  else ok raw1
partial_fixpoint

/-- [aspis_r1_mask_extraction_probe::field::qm31_m31_dot]: loop 2:
    Source: 'src/field.rs', lines 1474:8-1481:9
    Visibility: public -/
@[rust_loop]
def field.qm31_m31_dot_loop1_loop0
  (iter : core.ops.range.Range Std.Usize) (weights : Slice field.QM31)
  (values : Slice field.M31) (raw1 : Array Std.U64 4#usize) :
  Result (Array Std.U64 4#usize)
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok raw1
  | some index =>
    let m ← Slice.index_usize values index
    let value ← lift (UScalar.cast .U64 m)
    let weight ← Slice.index_usize weights index
    let i := weight.c0.a
    let i1 ← lift (UScalar.cast .U64 i)
    let i2 ← i1 * value
    let i3 ← Array.index_usize raw1 0#usize
    let i4 ← i3 + i2
    let raw2 ← Array.update raw1 0#usize i4
    let i5 := weight.c0.b
    let i6 ← lift (UScalar.cast .U64 i5)
    let i7 ← i6 * value
    let i8 ← Array.index_usize raw2 1#usize
    let i9 ← i8 + i7
    let raw3 ← Array.update raw2 1#usize i9
    let i10 := weight.c1.a
    let i11 ← lift (UScalar.cast .U64 i10)
    let i12 ← i11 * value
    let i13 ← Array.index_usize raw3 2#usize
    let i14 ← i13 + i12
    let raw4 ← Array.update raw3 2#usize i14
    let i15 := weight.c1.b
    let i16 ← lift (UScalar.cast .U64 i15)
    let i17 ← i16 * value
    let i18 ← Array.index_usize raw4 3#usize
    let i19 ← i18 + i17
    let a ← Array.update raw4 3#usize i19
    field.qm31_m31_dot_loop1_loop0 iter1 weights values a
partial_fixpoint

/-- [aspis_r1_mask_extraction_probe::field::qm31_m31_dot]: loop 3:
    Source: 'src/field.rs', lines 1482:8-1484:9
    Visibility: public -/
@[rust_loop]
def field.qm31_m31_dot_loop1_loop1
  (iter : core.ops.range.Range Std.Usize) (sums : Array Std.U64 4#usize)
  (raw1 : Array Std.U64 4#usize) :
  Result (Array Std.U64 4#usize)
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok sums
  | some index =>
    let i ← Array.index_usize raw1 index
    let m ← field.M31.reduce_u64 i
    let i1 ← lift (UScalar.cast .U64 m)
    let i2 ← Array.index_usize sums index
    let i3 ← i2 + i1
    let a ← Array.update sums index i3
    field.qm31_m31_dot_loop1_loop1 iter1 a raw1
partial_fixpoint

/-- [aspis_r1_mask_extraction_probe::field::qm31_m31_dot]: loop 1:
    Source: 'src/field.rs', lines 1471:4-1485:5
    Visibility: public -/
@[rust_loop]
def field.qm31_m31_dot_loop1
  (iter : core.iter.adapters.step_by.StepBy (core.ops.range.Range Std.Usize))
  (weights : Slice field.QM31) (values : Slice field.M31)
  (sums : Array Std.U64 4#usize) :
  Result (Array Std.U64 4#usize)
  := do
  let (o, iter1) ←
    core.iter.adapters.step_by.IteratorStepBy.next
      (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize) iter
  match o with
  | none => ok sums
  | some start =>
    let i ← start + 4#usize
    let i1 := Slice.len weights
    let end1 ← core.cmp.min core.cmp.OrdUsize i i1
    let raw1 := Array.repeat 4#usize 0#u64
    let raw2 ←
      field.qm31_m31_dot_loop1_loop0 { start, «end» := end1 } weights values
        raw1
    let sums1 ←
      field.qm31_m31_dot_loop1_loop1 { start := 0#usize, «end» := 4#usize }
        sums raw2
    field.qm31_m31_dot_loop1 iter1 weights values sums1
partial_fixpoint

/-- [aspis_r1_mask_extraction_probe::field::qm31_m31_dot]:
    Source: 'src/field.rs', lines 1447:0-1490:1
    Visibility: public -/
def field.qm31_m31_dot
  (weights : Slice field.QM31) (values : Slice field.M31) :
  Result field.QM31
  := do
  let left_val := Slice.len weights
  let right_val := Slice.len values
  massert (left_val = right_val)
  let i := Slice.len weights
  if i <= 4#usize
  then
    let raw1 := Array.repeat 4#usize 0#u64
    let raw2 ← field.qm31_m31_dot_loop0 weights values raw1 0#usize
    let i1 ← Array.index_usize raw2 0#usize
    let m ← field.M31.reduce_u64 i1
    let i2 ← Array.index_usize raw2 1#usize
    let m1 ← field.M31.reduce_u64 i2
    let c ← field.CM31.new m m1
    let i3 ← Array.index_usize raw2 2#usize
    let m2 ← field.M31.reduce_u64 i3
    let i4 ← Array.index_usize raw2 3#usize
    let m3 ← field.M31.reduce_u64 i4
    let c1 ← field.CM31.new m2 m3
    ok { c0 := c, c1 }
  else
    let sums := Array.repeat 4#usize 0#u64
    let i1 := Slice.len weights
    let iter ←
      core.iter.traits.iterator.Iterator.step_by.trait_default
        (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize)
        { start := 0#usize, «end» := i1 } 4#usize
    let sums1 ← field.qm31_m31_dot_loop1 iter weights values sums
    let i2 ← Array.index_usize sums1 0#usize
    let m ← field.M31.reduce_u64 i2
    let i3 ← Array.index_usize sums1 1#usize
    let m1 ← field.M31.reduce_u64 i3
    let c ← field.CM31.new m m1
    let i4 ← Array.index_usize sums1 2#usize
    let m2 ← field.M31.reduce_u64 i4
    let i5 ← Array.index_usize sums1 3#usize
    let m3 ← field.M31.reduce_u64 i5
    let c1 ← field.CM31.new m2 m3
    ok { c0 := c, c1 }


end AspisR1SelectedMaskProbe
