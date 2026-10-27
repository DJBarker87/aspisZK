-- Exact generated declarations from the pinned G packer output; framing only.
import Aeneas.Std
import Aeneas.Tactic.RustAttributes
import AspisR1SelectedMaskProbe.Types
import AspisR1SelectedMaskProbe.Funs
import RPv_SelectedClaimGatherSlice
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
namespace AspisR1SelectedMaskProbe

/-- [aspis_r1_mask_extraction_probe::field::qm31_pack_base4::closure]
    Source: 'src/field.rs', lines 1054:15-1054:46 -/
@[reducible]
def field.qm31_pack_base4.closure := Unit


/-- [aspis_r1_mask_extraction_probe::field::qm31_pack_base4::{impl core::ops::function::Fn<(aspis_r1_mask_extraction_probe::field::M31,), u64> for aspis_r1_mask_extraction_probe::field::qm31_pack_base4::closure}::call]:
    Source: 'src/field.rs', lines 1054:15-1054:46 -/
def field.qm31_pack_base4.closure.Insts.CoreOpsFunctionFnTupleM31U64.call
  (c : field.qm31_pack_base4.closure) (tupled_args : field.M31) :
  Result Std.U64
  := do
  ok (core.convert.num.FromU64U32.from tupled_args)


/-- [aspis_r1_mask_extraction_probe::field::qm31_pack_base4]:
    Source: 'src/field.rs', lines 1048:0-1077:1
    Visibility: public -/
def field.qm31_pack_base4 (values : Slice field.QM31) : Result field.QM31 := do
  let i := Slice.len values
  massert (i <= 4#usize)
  let padded := Array.repeat 4#usize field.QM31.ZERO
  let i1 := Slice.len values
  let (s, index_mut_back) ←
    core.array.Array.index_mut (core.ops.index.IndexMutSlice
      (core.slice.index.SliceIndexRangeToUsizeSlice field.QM31)) padded
      { «end» := i1 }
  let s1 ←
    core.slice.Slice.copy_from_slice field.QM31.Insts.CoreMarkerCopy s values
  let padded1 := index_mut_back s1
  let v0 ← Array.index_usize padded1 0#usize
  let v1 ← Array.index_usize padded1 1#usize
  let v2 ← Array.index_usize padded1 2#usize
  let v3 ← Array.index_usize padded1 3#usize
  let p ← lift (core.convert.num.FromU64U32.from field.P)
  let i2 ←
    field.qm31_pack_base4.closure.Insts.CoreOpsFunctionFnTupleM31U64.call ()
      v0.c0.a
  let i3 ←
    field.qm31_pack_base4.closure.Insts.CoreOpsFunctionFnTupleM31U64.call ()
      v1.c0.b
  let i4 ← p - i3
  let i5 ← i2 + i4
  let i6 ←
    field.qm31_pack_base4.closure.Insts.CoreOpsFunctionFnTupleM31U64.call ()
      v2.c1.a
  let i7 ← 2#u64 * i6
  let i8 ← i5 + i7
  let i9 ←
    field.qm31_pack_base4.closure.Insts.CoreOpsFunctionFnTupleM31U64.call ()
      v2.c1.b
  let i10 ← p - i9
  let i11 ← i8 + i10
  let i12 ←
    field.qm31_pack_base4.closure.Insts.CoreOpsFunctionFnTupleM31U64.call ()
      v3.c1.a
  let i13 ← p - i12
  let i14 ← i11 + i13
  let i15 ← 2#u64 * p
  let i16 ←
    field.qm31_pack_base4.closure.Insts.CoreOpsFunctionFnTupleM31U64.call ()
      v3.c1.b
  let i17 ← 2#u64 * i16
  let i18 ← i15 - i17
  let c0_a ← i14 + i18
  let i19 ←
    field.qm31_pack_base4.closure.Insts.CoreOpsFunctionFnTupleM31U64.call ()
      v0.c0.b
  let i20 ←
    field.qm31_pack_base4.closure.Insts.CoreOpsFunctionFnTupleM31U64.call ()
      v1.c0.a
  let i21 ← i19 + i20
  let i22 ← i21 + i6
  let i23 ← 2#u64 * i9
  let i24 ← i22 + i23
  let i25 ← 2#u64 * i12
  let i26 ← i24 + i25
  let i27 ← p - i16
  let c0_b ← i26 + i27
  let i28 ←
    field.qm31_pack_base4.closure.Insts.CoreOpsFunctionFnTupleM31U64.call ()
      v0.c1.a
  let i29 ←
    field.qm31_pack_base4.closure.Insts.CoreOpsFunctionFnTupleM31U64.call ()
      v1.c1.b
  let i30 ← p - i29
  let i31 ← i28 + i30
  let i32 ←
    field.qm31_pack_base4.closure.Insts.CoreOpsFunctionFnTupleM31U64.call ()
      v2.c0.a
  let i33 ← i31 + i32
  let i34 ←
    field.qm31_pack_base4.closure.Insts.CoreOpsFunctionFnTupleM31U64.call ()
      v3.c0.b
  let i35 ← p - i34
  let c1_a ← i33 + i35
  let i36 ←
    field.qm31_pack_base4.closure.Insts.CoreOpsFunctionFnTupleM31U64.call ()
      v0.c1.b
  let i37 ←
    field.qm31_pack_base4.closure.Insts.CoreOpsFunctionFnTupleM31U64.call ()
      v1.c1.a
  let i38 ← i36 + i37
  let i39 ←
    field.qm31_pack_base4.closure.Insts.CoreOpsFunctionFnTupleM31U64.call ()
      v2.c0.b
  let i40 ← i38 + i39
  let i41 ←
    field.qm31_pack_base4.closure.Insts.CoreOpsFunctionFnTupleM31U64.call ()
      v3.c0.a
  let c1_b ← i40 + i41
  let m ← field.M31.reduce_u64 c0_a
  let m1 ← field.M31.reduce_u64 c0_b
  let c ← field.CM31.new m m1
  let m2 ← field.M31.reduce_u64 c1_a
  let m3 ← field.M31.reduce_u64 c1_b
  let c1 ← field.CM31.new m2 m3
  ok { c0 := c, c1 }


end AspisR1SelectedMaskProbe
