import FIq_Native01
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.unusedVariables false
noncomputable section
namespace FIq_Native
/-- [aspis_r1_mask_extraction_probe::field::qm31_sum_products3_prepared]:
    Source: 'src/field.rs', lines 678:0-703:1
    Visibility: public -/
def field.qm31_sum_products3_prepared
  (left : Array field.PreparedQm31Multiplier 3#usize)
  (right : Array field.QM31 3#usize) :
  Result field.QM31
  := do
  let a := Array.repeat 3#usize 0#u64
  let sums := Array.repeat 3#usize a
  let sums1 ←
    field.qm31_sum_products3_prepared_loop0
      { start := 0#usize, «end» := 3#usize } left right sums
  field.qm31_from_karatsuba_channel_sums sums1

/-- [aspis_r1_mask_extraction_probe::field::{aspis_r1_mask_extraction_probe::field::QM31}::ZERO]
    Source: 'src/field.rs', lines 869:4-878:6
    Visibility: public -/
@[global_simps, irreducible]
def field.QM31.ZERO : field.QM31 :=
  { c0 := { a := 0#u32, b := 0#u32 }, c1 := { a := 0#u32, b := 0#u32 } }

/-- [aspis_r1_mask_extraction_probe::field::{aspis_r1_mask_extraction_probe::field::QM31}::ONE]
    Source: 'src/field.rs', lines 879:4-888:6
    Visibility: public -/
@[global_simps, irreducible]
def field.QM31.ONE : field.QM31 :=
  { c0 := { a := 1#u32, b := 0#u32 }, c1 := { a := 0#u32, b := 0#u32 } }

/-- [aspis_r1_mask_extraction_probe::field::{aspis_r1_mask_extraction_probe::field::QM31}::from_cm31]:
    Source: 'src/field.rs', lines 891:4-893:5
    Visibility: public -/
def field.QM31.from_cm31 (c0 : field.CM31) : Result field.QM31 := do
  ok { c0, c1 := field.CM31.ZERO }

/-- [aspis_r1_mask_extraction_probe::field::{aspis_r1_mask_extraction_probe::field::QM31}::add]:
    Source: 'src/field.rs', lines 896:4-903:5
    Visibility: public -/
def field.QM31.add
  (self : field.QM31) (rhs : field.QM31) : Result field.QM31 := do
  let c ← field.CM31.add self.c0 rhs.c0
  let c1 ← field.CM31.add self.c1 rhs.c1
  ok { c0 := c, c1 }

/-- [aspis_r1_mask_extraction_probe::field::{aspis_r1_mask_extraction_probe::field::QM31}::sub]:
    Source: 'src/field.rs', lines 906:4-913:5
    Visibility: public -/
def field.QM31.sub
  (self : field.QM31) (rhs : field.QM31) : Result field.QM31 := do
  let c ← field.CM31.sub self.c0 rhs.c0
  let c1 ← field.CM31.sub self.c1 rhs.c1
  ok { c0 := c, c1 }

/-- [aspis_r1_mask_extraction_probe::field::{aspis_r1_mask_extraction_probe::field::QM31}::mul]:
    Source: 'src/field.rs', lines 935:4-945:5
    Visibility: public -/
def field.QM31.mul
  (self : field.QM31) (rhs : field.QM31) : Result field.QM31 := do
  let m0 ← field.CM31.mul self.c0 rhs.c0
  let m1 ← field.CM31.mul self.c1 rhs.c1
  let c ← field.CM31.add self.c0 self.c1
  let c1 ← field.CM31.add rhs.c0 rhs.c1
  let m2 ← field.CM31.mul c c1
  let c2 ← field.mul_by_r m1
  let c3 ← field.CM31.add m0 c2
  let c4 ← field.CM31.sub m2 m0
  let c5 ← field.CM31.sub c4 m1
  ok { c0 := c3, c1 := c5 }

/-- [aspis_r1_mask_extraction_probe::field::{aspis_r1_mask_extraction_probe::field::QM31}::square]:
    Source: 'src/field.rs', lines 951:4-960:5
    Visibility: public -/
def field.QM31.square (self : field.QM31) : Result field.QM31 := do
  let c0_square ← field.CM31.square self.c0
  let c1_square ← field.CM31.square self.c1
  let c ← field.mul_by_r c1_square
  let c1 ← field.CM31.add c0_square c
  let c2 ← field.CM31.mul self.c0 self.c1
  let c3 ← field.CM31.double c2
  ok { c0 := c1, c1 := c3 }

/-- [aspis_r1_mask_extraction_probe::field::{aspis_r1_mask_extraction_probe::field::QM31}::mul_m31]:
    Source: 'src/field.rs', lines 975:4-982:5
    Visibility: public -/
def field.QM31.mul_m31
  (self : field.QM31) (rhs : field.M31) : Result field.QM31 := do
  let c ← field.CM31.mul_m31 self.c0 rhs
  let c1 ← field.CM31.mul_m31 self.c1 rhs
  ok { c0 := c, c1 }

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

/-- [aspis_r1_mask_extraction_probe::state_only_hiding::STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS]
    Source: 'src/state_only_hiding.rs', lines 13:0-13:61
    Visibility: public -/
@[global_simps, irreducible]
def state_only_hiding.STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS : Std.Usize :=
  10#usize

/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::r0::{aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::r0::Public<'a>}::terminal_qm31::{impl core::ops::function::FnOnce<(aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::PoolV1PairForestSemanticTerminalErrorV1,), aspis_r1_mask_extraction_probe::state_only_prefix::r0::Error> for aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::r0::{aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::r0::Public<'a>}::terminal_qm31::closure#2<'a>}::call_once]:
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 2098:21-2098:38 -/
def
  pool_v1.pair_forest_semantic_terminal.r0.Public.terminal_qm31.closure_2.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairForestSemanticTerminalErrorV1Error.call_once
  (c : pool_v1.pair_forest_semantic_terminal.r0.Public.terminal_qm31.closure_2)
  (tupled_args :
  pool_v1.pair_forest_semantic_terminal.PoolV1PairForestSemanticTerminalErrorV1)
  :
  Result state_only_prefix.r0.Error
  := do
  ok state_only_prefix.r0.Error.Public

/-- Trait implementation: [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::r0::{aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::r0::Public<'a>}::terminal_qm31::{impl core::ops::function::FnOnce<(aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::PoolV1PairForestSemanticTerminalErrorV1,), aspis_r1_mask_extraction_probe::state_only_prefix::r0::Error> for aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::r0::{aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::r0::Public<'a>}::terminal_qm31::closure#2<'a>}]
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 2098:21-2098:38 -/
@[reducible]
def
  pool_v1.pair_forest_semantic_terminal.r0.Public.terminal_qm31.closure_2.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairForestSemanticTerminalErrorV1Error
  : core.ops.function.FnOnce
  pool_v1.pair_forest_semantic_terminal.r0.Public.terminal_qm31.closure_2
  pool_v1.pair_forest_semantic_terminal.PoolV1PairForestSemanticTerminalErrorV1
  state_only_prefix.r0.Error := {
  call_once :=
    pool_v1.pair_forest_semantic_terminal.r0.Public.terminal_qm31.closure_2.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairForestSemanticTerminalErrorV1Error.call_once
}

/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::r0::{aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::r0::Public<'a>}::terminal_qm31::{impl core::ops::function::FnOnce<((aspis_r1_mask_extraction_probe::field::QM31, [aspis_r1_mask_extraction_probe::field::QM31; 16usize], [aspis_r1_mask_extraction_probe::field::QM31; 10usize], aspis_r1_mask_extraction_probe::field::QM31),), aspis_r1_mask_extraction_probe::field::QM31> for aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::r0::{aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::r0::Public<'a>}::terminal_qm31::closure#1<'a>}::call_once]:
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 2097:17-2097:32 -/
def
  pool_v1.pair_forest_semantic_terminal.r0.Public.terminal_qm31.closure_1.Insts.CoreOpsFunctionFnOnceTupleTupleQM31ArrayQM3116ArrayQM3110QM31QM31.call_once
  (c : pool_v1.pair_forest_semantic_terminal.r0.Public.terminal_qm31.closure_1)
  (tupled_args : (field.QM31 × (Array field.QM31 16#usize) × (Array
  field.QM31 10#usize) × field.QM31)) :
  Result field.QM31
  := do
  let (q, _, _, _) := tupled_args
  ok q

/-- Trait implementation: [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::r0::{aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::r0::Public<'a>}::terminal_qm31::{impl core::ops::function::FnOnce<((aspis_r1_mask_extraction_probe::field::QM31, [aspis_r1_mask_extraction_probe::field::QM31; 16usize], [aspis_r1_mask_extraction_probe::field::QM31; 10usize], aspis_r1_mask_extraction_probe::field::QM31),), aspis_r1_mask_extraction_probe::field::QM31> for aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::r0::{aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::r0::Public<'a>}::terminal_qm31::closure#1<'a>}]
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 2097:17-2097:32 -/
@[reducible]
def
  pool_v1.pair_forest_semantic_terminal.r0.Public.terminal_qm31.closure_1.Insts.CoreOpsFunctionFnOnceTupleTupleQM31ArrayQM3116ArrayQM3110QM31QM31
  : core.ops.function.FnOnce
  pool_v1.pair_forest_semantic_terminal.r0.Public.terminal_qm31.closure_1
  (field.QM31 × (Array field.QM31 16#usize) × (Array field.QM31 10#usize) ×
  field.QM31) field.QM31 := {
  call_once :=
    pool_v1.pair_forest_semantic_terminal.r0.Public.terminal_qm31.closure_1.Insts.CoreOpsFunctionFnOnceTupleTupleQM31ArrayQM3116ArrayQM3110QM31QM31.call_once
}

/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::r0::{aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::r0::Public<'a>}::terminal_qm31::{impl core::ops::function::FnMut<(usize,), aspis_r1_mask_extraction_probe::field::QM31> for aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::r0::{aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::r0::Public<'a>}::terminal_qm31::closure<'a, '_1>}::call_mut]:
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 2086:74-2086:100 -/
def
  pool_v1.pair_forest_semantic_terminal.r0.Public.terminal_qm31.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
  (c : pool_v1.pair_forest_semantic_terminal.r0.Public.terminal_qm31.closure)
  (tupled_args : Std.Usize) :
  Result (field.QM31 ×
    pool_v1.pair_forest_semantic_terminal.r0.Public.terminal_qm31.closure)
  := do
  let i ← tupled_args / 28#usize
  let i1 ← tupled_args % 28#usize
  let a ← Array.index_usize c i
  let q ← Array.index_usize a i1
  ok (q, c)

/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::r0::{aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::r0::Public<'a>}::terminal_qm31::{impl core::ops::function::FnOnce<(usize,), aspis_r1_mask_extraction_probe::field::QM31> for aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::r0::{aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::r0::Public<'a>}::terminal_qm31::closure<'a, '_1>}::call_once]:
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 2086:74-2086:100 -/
def
  pool_v1.pair_forest_semantic_terminal.r0.Public.terminal_qm31.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31.call_once
  (c : pool_v1.pair_forest_semantic_terminal.r0.Public.terminal_qm31.closure)
  (i : Std.Usize) :
  Result field.QM31
  := do
  let (q, _) ←
    pool_v1.pair_forest_semantic_terminal.r0.Public.terminal_qm31.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
      c i
  ok q


end FIq_Native
