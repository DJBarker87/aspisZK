import RPu_FIq_Native04
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.unusedVariables false
noncomputable section
namespace FIq_Native
/-- [aspis_r1_mask_extraction_probe::state_only_poseidon::interpolate_three_constant_limb]:
    Source: 'src/statement/state_only_poseidon.rs', lines 421:0-434:1 -/
def state_only_poseidon.interpolate_three_constant_limb
  (weight0 : Std.U32) (weight1 : Std.U32) (weight2 : Std.U32)
  (constant0 : Std.U32) (constant1 : Std.U32) (constant2 : Std.U32) :
  Result field.M31
  := do
  let i ← lift (core.convert.num.FromU64U32.from weight0)
  let i1 ← lift (core.convert.num.FromU64U32.from constant0)
  let i2 ← i * i1
  let i3 ← lift (core.convert.num.FromU64U32.from weight1)
  let i4 ← lift (core.convert.num.FromU64U32.from constant1)
  let i5 ← i3 * i4
  let i6 ← i2 + i5
  let i7 ← lift (core.convert.num.FromU64U32.from weight2)
  let i8 ← lift (core.convert.num.FromU64U32.from constant2)
  let i9 ← i7 * i8
  let i10 ← i6 + i9
  field.M31.reduce_u64 i10

/-- [aspis_r1_mask_extraction_probe::state_only_poseidon::interpolate_three_constant_columns]: loop 0:
    Source: 'src/statement/state_only_poseidon.rs', lines 445:4-485:5 -/
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
    Source: 'src/statement/state_only_poseidon.rs', lines 437:0-487:1 -/
def state_only_poseidon.interpolate_three_constant_columns
  (weights : Array field.QM31 3#usize) (column0 : Array Std.U32 16#usize)
  (column1 : Array Std.U32 16#usize) (column2 : Array Std.U32 16#usize) :
  Result (Array field.QM31 16#usize)
  := do
  let output := Array.repeat 16#usize field.QM31.ZERO
  state_only_poseidon.interpolate_three_constant_columns_loop weights column0
    column1 column2 output 0#usize

/-- [aspis_r1_mask_extraction_probe::state_only_poseidon::external_linear_packed::{impl core::ops::function::FnMut<(aspis_r1_mask_extraction_probe::field::QM31,), aspis_r1_mask_extraction_probe::field::QM31> for aspis_r1_mask_extraction_probe::state_only_poseidon::external_linear_packed::closure<'_0>}::call_mut]:
    Source: 'src/statement/state_only_poseidon.rs', lines 304:21-304:43 -/
def
  state_only_poseidon.external_linear_packed.closure.Insts.CoreOpsFunctionFnMutTupleQM31QM31.call_mut
  (c : state_only_poseidon.external_linear_packed.closure)
  (tupled_args : field.QM31) :
  Result (field.QM31 × state_only_poseidon.external_linear_packed.closure)
  := do
  let q ← field.QM31.add tupled_args c
  ok (q, c)

/-- [aspis_r1_mask_extraction_probe::state_only_poseidon::external_linear_packed::{impl core::ops::function::FnOnce<(aspis_r1_mask_extraction_probe::field::QM31,), aspis_r1_mask_extraction_probe::field::QM31> for aspis_r1_mask_extraction_probe::state_only_poseidon::external_linear_packed::closure<'_0>}::call_once]:
    Source: 'src/statement/state_only_poseidon.rs', lines 304:21-304:43 -/
def
  state_only_poseidon.external_linear_packed.closure.Insts.CoreOpsFunctionFnOnceTupleQM31QM31.call_once
  (c : state_only_poseidon.external_linear_packed.closure) (q : field.QM31) :
  Result field.QM31
  := do
  let (q1, _) ←
    state_only_poseidon.external_linear_packed.closure.Insts.CoreOpsFunctionFnMutTupleQM31QM31.call_mut
      c q
  ok q1

/-- Trait implementation: [aspis_r1_mask_extraction_probe::state_only_poseidon::external_linear_packed::{impl core::ops::function::FnOnce<(aspis_r1_mask_extraction_probe::field::QM31,), aspis_r1_mask_extraction_probe::field::QM31> for aspis_r1_mask_extraction_probe::state_only_poseidon::external_linear_packed::closure<'_0>}]
    Source: 'src/statement/state_only_poseidon.rs', lines 304:21-304:43 -/
@[reducible]
def
  state_only_poseidon.external_linear_packed.closure.Insts.CoreOpsFunctionFnOnceTupleQM31QM31
  : core.ops.function.FnOnce state_only_poseidon.external_linear_packed.closure
  field.QM31 field.QM31 := {
  call_once :=
    state_only_poseidon.external_linear_packed.closure.Insts.CoreOpsFunctionFnOnceTupleQM31QM31.call_once
}

/-- Trait implementation: [aspis_r1_mask_extraction_probe::state_only_poseidon::external_linear_packed::{impl core::ops::function::FnMut<(aspis_r1_mask_extraction_probe::field::QM31,), aspis_r1_mask_extraction_probe::field::QM31> for aspis_r1_mask_extraction_probe::state_only_poseidon::external_linear_packed::closure<'_0>}]
    Source: 'src/statement/state_only_poseidon.rs', lines 304:21-304:43 -/
@[reducible]
def
  state_only_poseidon.external_linear_packed.closure.Insts.CoreOpsFunctionFnMutTupleQM31QM31
  : core.ops.function.FnMut state_only_poseidon.external_linear_packed.closure
  field.QM31 field.QM31 := {
  FnOnceInst :=
    state_only_poseidon.external_linear_packed.closure.Insts.CoreOpsFunctionFnOnceTupleQM31QM31
  call_mut :=
    state_only_poseidon.external_linear_packed.closure.Insts.CoreOpsFunctionFnMutTupleQM31QM31.call_mut
}

/-- [aspis_r1_mask_extraction_probe::state_only_poseidon::external_local_packed_raw::closure::{impl core::ops::function::FnMut<(usize,), u64> for aspis_r1_mask_extraction_probe::state_only_poseidon::external_local_packed_raw::closure::closure<'_0, '_1>}::call_mut]:
    Source: 'src/statement/state_only_poseidon.rs', lines 224:48-236:9 -/
def
  state_only_poseidon.external_local_packed_raw.closure.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64.call_mut
  (c : state_only_poseidon.external_local_packed_raw.closure.closure)
  (tupled_args : Std.Usize) :
  Result (Std.U64 ×
    state_only_poseidon.external_local_packed_raw.closure.closure)
  := do
  let (a, i) := c
  let a1 ← Array.index_usize a 0#usize
  let i1 ← Array.index_usize a1 tupled_args
  let a2 ← lift (core.convert.num.FromU64U32.from i1)
  let a3 ← Array.index_usize a 1#usize
  let i2 ← Array.index_usize a3 tupled_args
  let b ← lift (core.convert.num.FromU64U32.from i2)
  let a4 ← Array.index_usize a 2#usize
  let i3 ← Array.index_usize a4 tupled_args
  let c1 ← lift (core.convert.num.FromU64U32.from i3)
  let a5 ← Array.index_usize a 3#usize
  let i4 ← Array.index_usize a5 tupled_args
  let d ← lift (core.convert.num.FromU64U32.from i4)
  match i.val with
  | 0 =>
    let i5 ← 2#u64 * a2
    let i6 ← 3#u64 * b
    let i7 ← i5 + i6
    let i8 ← i7 + c1
    let i9 ← i8 + d
    ok (i9, c)
  | 1 =>
    let i5 ← 2#u64 * b
    let i6 ← a2 + i5
    let i7 ← 3#u64 * c1
    let i8 ← i6 + i7
    let i9 ← i8 + d
    ok (i9, c)
  | 2 =>
    let i5 ← a2 + b
    let i6 ← 2#u64 * c1
    let i7 ← i5 + i6
    let i8 ← 3#u64 * d
    let i9 ← i7 + i8
    ok (i9, c)
  | 3 =>
    let i5 ← 3#u64 * a2
    let i6 ← i5 + b
    let i7 ← i6 + c1
    let i8 ← 2#u64 * d
    let i9 ← i7 + i8
    ok (i9, c)
  | _ => fail panic

/-- [aspis_r1_mask_extraction_probe::state_only_poseidon::external_local_packed_raw::closure::{impl core::ops::function::FnOnce<(usize,), u64> for aspis_r1_mask_extraction_probe::state_only_poseidon::external_local_packed_raw::closure::closure<'_0, '_1>}::call_once]:
    Source: 'src/statement/state_only_poseidon.rs', lines 224:48-236:9 -/
def
  state_only_poseidon.external_local_packed_raw.closure.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeU64.call_once
  (c : state_only_poseidon.external_local_packed_raw.closure.closure)
  (i : Std.Usize) :
  Result Std.U64
  := do
  let (i1, _) ←
    state_only_poseidon.external_local_packed_raw.closure.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64.call_mut
      c i
  ok i1

/-- Trait implementation: [aspis_r1_mask_extraction_probe::state_only_poseidon::external_local_packed_raw::closure::{impl core::ops::function::FnOnce<(usize,), u64> for aspis_r1_mask_extraction_probe::state_only_poseidon::external_local_packed_raw::closure::closure<'_0, '_1>}]
    Source: 'src/statement/state_only_poseidon.rs', lines 224:48-236:9 -/
@[reducible]
def
  state_only_poseidon.external_local_packed_raw.closure.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeU64
  : core.ops.function.FnOnce
  state_only_poseidon.external_local_packed_raw.closure.closure Std.Usize
  Std.U64 := {
  call_once :=
    state_only_poseidon.external_local_packed_raw.closure.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeU64.call_once
}

/-- Trait implementation: [aspis_r1_mask_extraction_probe::state_only_poseidon::external_local_packed_raw::closure::{impl core::ops::function::FnMut<(usize,), u64> for aspis_r1_mask_extraction_probe::state_only_poseidon::external_local_packed_raw::closure::closure<'_0, '_1>}]
    Source: 'src/statement/state_only_poseidon.rs', lines 224:48-236:9 -/
@[reducible]
def
  state_only_poseidon.external_local_packed_raw.closure.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64
  : core.ops.function.FnMut
  state_only_poseidon.external_local_packed_raw.closure.closure Std.Usize
  Std.U64 := {
  FnOnceInst :=
    state_only_poseidon.external_local_packed_raw.closure.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeU64
  call_mut :=
    state_only_poseidon.external_local_packed_raw.closure.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64.call_mut
}

/-- [aspis_r1_mask_extraction_probe::state_only_poseidon::external_local_packed_raw::{impl core::ops::function::FnMut<(usize,), [u64; 4usize]> for aspis_r1_mask_extraction_probe::state_only_poseidon::external_local_packed_raw::closure<'_0>}::call_mut]:
    Source: 'src/statement/state_only_poseidon.rs', lines 223:76-237:5 -/
def
  state_only_poseidon.external_local_packed_raw.closure.Insts.CoreOpsFunctionFnMutTupleUsizeArrayU644.call_mut
  (c : state_only_poseidon.external_local_packed_raw.closure)
  (tupled_args : Std.Usize) :
  Result ((Array Std.U64 4#usize) ×
    state_only_poseidon.external_local_packed_raw.closure)
  := do
  let a ←
    array_from_fn_copy 4#usize core.marker.CopyU64
      state_only_poseidon.external_local_packed_raw.closure.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64
      0#u64 (c, tupled_args)
  ok (a, c)

/-- [aspis_r1_mask_extraction_probe::state_only_poseidon::external_local_packed_raw::{impl core::ops::function::FnOnce<(usize,), [u64; 4usize]> for aspis_r1_mask_extraction_probe::state_only_poseidon::external_local_packed_raw::closure<'_0>}::call_once]:
    Source: 'src/statement/state_only_poseidon.rs', lines 223:76-237:5 -/
def
  state_only_poseidon.external_local_packed_raw.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeArrayU644.call_once
  (c : state_only_poseidon.external_local_packed_raw.closure) (i : Std.Usize) :
  Result (Array Std.U64 4#usize)
  := do
  let (a, _) ←
    state_only_poseidon.external_local_packed_raw.closure.Insts.CoreOpsFunctionFnMutTupleUsizeArrayU644.call_mut
      c i
  ok a

/-- Trait implementation: [aspis_r1_mask_extraction_probe::state_only_poseidon::external_local_packed_raw::{impl core::ops::function::FnOnce<(usize,), [u64; 4usize]> for aspis_r1_mask_extraction_probe::state_only_poseidon::external_local_packed_raw::closure<'_0>}]
    Source: 'src/statement/state_only_poseidon.rs', lines 223:76-237:5 -/
@[reducible]
def
  state_only_poseidon.external_local_packed_raw.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeArrayU644
  : core.ops.function.FnOnce
  state_only_poseidon.external_local_packed_raw.closure Std.Usize (Array
  Std.U64 4#usize) := {
  call_once :=
    state_only_poseidon.external_local_packed_raw.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeArrayU644.call_once
}

/-- Trait implementation: [aspis_r1_mask_extraction_probe::state_only_poseidon::external_local_packed_raw::{impl core::ops::function::FnMut<(usize,), [u64; 4usize]> for aspis_r1_mask_extraction_probe::state_only_poseidon::external_local_packed_raw::closure<'_0>}]
    Source: 'src/statement/state_only_poseidon.rs', lines 223:76-237:5 -/
@[reducible]
def
  state_only_poseidon.external_local_packed_raw.closure.Insts.CoreOpsFunctionFnMutTupleUsizeArrayU644
  : core.ops.function.FnMut
  state_only_poseidon.external_local_packed_raw.closure Std.Usize (Array
  Std.U64 4#usize) := {
  FnOnceInst :=
    state_only_poseidon.external_local_packed_raw.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeArrayU644
  call_mut :=
    state_only_poseidon.external_local_packed_raw.closure.Insts.CoreOpsFunctionFnMutTupleUsizeArrayU644.call_mut
}

/-- [aspis_r1_mask_extraction_probe::state_only_poseidon::EXTERNAL_LOCAL_LIMB_MODULUS_BOUND]
    Source: 'src/statement/state_only_poseidon.rs', lines 201:0-201:60 -/
@[global_simps, irreducible]
def state_only_poseidon.EXTERNAL_LOCAL_LIMB_MODULUS_BOUND
  : Result Std.U64 := do
  let i ← lift (UScalar.cast .U64 field.P)
  7#u64 * i

/-- [aspis_r1_mask_extraction_probe::state_only_poseidon::external_local_packed_raw]: loop 1:
    Source: 'src/statement/state_only_poseidon.rs', lines 242:8-245:9 -/
@[rust_loop]
def state_only_poseidon.external_local_packed_raw_loop0_loop0
  (local1 : Array (Array Std.U64 4#usize) 4#usize)
  (all_local_limbs_bounded : Bool) (output : Std.Usize) (limb : Std.Usize) :
  Result Bool
  := do
  if limb < 4#usize
  then
    let a ← Array.index_usize local1 output
    let i ← Array.index_usize a limb
    let i1 ← state_only_poseidon.EXTERNAL_LOCAL_LIMB_MODULUS_BOUND
    let limb1 ← limb + 1#usize
    state_only_poseidon.external_local_packed_raw_loop0_loop0 local1
      (all_local_limbs_bounded && (i < i1)) output limb1
  else ok all_local_limbs_bounded
partial_fixpoint

/-- [aspis_r1_mask_extraction_probe::state_only_poseidon::external_local_packed_raw]: loop 0:
    Source: 'src/statement/state_only_poseidon.rs', lines 240:4-247:5 -/
@[rust_loop]
def state_only_poseidon.external_local_packed_raw_loop0
  (local1 : Array (Array Std.U64 4#usize) 4#usize)
  (all_local_limbs_bounded : Bool) (output : Std.Usize) :
  Result Unit
  := do
  if output < 4#usize
  then
    let all_local_limbs_bounded1 ←
      state_only_poseidon.external_local_packed_raw_loop0_loop0 local1
        all_local_limbs_bounded output 0#usize
    let output1 ← output + 1#usize
    state_only_poseidon.external_local_packed_raw_loop0 local1
      all_local_limbs_bounded1 output1
  else ok ()
partial_fixpoint

/-- [aspis_r1_mask_extraction_probe::state_only_poseidon::external_local_packed_raw]:
    Source: 'src/statement/state_only_poseidon.rs', lines 221:0-266:1 -/
def state_only_poseidon.external_local_packed_raw
  (input : Array field.QM31 4#usize) : Result (Array Std.U64 4#usize) := do
  let input1 ←
    core.array.Array.map (BuiltinFnMut field.QM31 (Array Std.U32 4#usize))
      input (state_only_poseidon.extension_limbs)
  let a := Array.repeat 4#usize 0#u64
  let local1 ←
    array_from_fn_copy 4#usize (Array.Insts.CoreMarkerCopy 4#usize
      core.marker.CopyU64)
      state_only_poseidon.external_local_packed_raw.closure.Insts.CoreOpsFunctionFnMutTupleUsizeArrayU644
      a input1
  state_only_poseidon.external_local_packed_raw_loop0 local1 true 0#usize
  let bound ← state_only_poseidon.EXTERNAL_LOCAL_LIMB_MODULUS_BOUND
  let a1 ← Array.index_usize local1 0#usize
  let i ← Array.index_usize a1 0#usize
  let i1 ← 5#u64 * bound
  let i2 ← i + i1
  let a2 ← Array.index_usize local1 1#usize
  let i3 ← Array.index_usize a2 1#usize
  let i4 ← i2 - i3
  let a3 ← Array.index_usize local1 2#usize
  let i5 ← Array.index_usize a3 2#usize
  let i6 ← 2#u64 * i5
  let i7 ← i4 + i6
  let i8 ← Array.index_usize a3 3#usize
  let i9 ← i7 - i8
  let a4 ← Array.index_usize local1 3#usize
  let i10 ← Array.index_usize a4 2#usize
  let i11 ← i9 - i10
  let i12 ← Array.index_usize a4 3#usize
  let i13 ← 2#u64 * i12
  let i14 ← i11 - i13
  let i15 ← Array.index_usize a1 1#usize
  let i16 ← Array.index_usize a2 0#usize
  let i17 ← i15 + i16
  let i18 ← Array.index_usize a3 2#usize
  let i19 ← i17 + i18
  let i20 ← Array.index_usize a3 3#usize
  let i21 ← 2#u64 * i20
  let i22 ← i19 + i21
  let i23 ← Array.index_usize a4 2#usize
  let i24 ← 2#u64 * i23
  let i25 ← i22 + i24
  let i26 ← i25 + bound
  let i27 ← Array.index_usize a4 3#usize
  let i28 ← i26 - i27
  let i29 ← Array.index_usize a1 2#usize
  let i30 ← 2#u64 * bound
  let i31 ← i29 + i30
  let i32 ← Array.index_usize a2 3#usize
  let i33 ← i31 - i32
  let i34 ← Array.index_usize a3 0#usize
  let i35 ← i33 + i34
  let i36 ← Array.index_usize a4 1#usize
  let i37 ← i35 - i36
  let i38 ← Array.index_usize a1 3#usize
  let i39 ← Array.index_usize a2 2#usize
  let i40 ← i38 + i39
  let i41 ← Array.index_usize a3 1#usize
  let i42 ← i40 + i41
  let i43 ← Array.index_usize a4 0#usize
  let i44 ← i42 + i43
  ok (Array.make 4#usize [ i14, i28, i37, i44 ])

/-- [aspis_r1_mask_extraction_probe::state_only_poseidon::external_local_packed]:
    Source: 'src/statement/state_only_poseidon.rs', lines 269:0-271:1 -/
def state_only_poseidon.external_local_packed
  (input : Array field.QM31 4#usize) : Result field.QM31 := do
  let a ← state_only_poseidon.external_local_packed_raw input
  state_only_poseidon.extension_from_raw_limbs a

/-- [aspis_r1_mask_extraction_probe::state_only_poseidon::external_linear_packed]: loop 0:
    Source: 'src/statement/state_only_poseidon.rs', lines 288:4-298:5 -/
@[rust_loop]
def state_only_poseidon.external_linear_packed_loop
  (state : Array field.QM31 16#usize) (local_packed : Array field.QM31 4#usize)
  (group : Std.Usize) :
  Result (Array field.QM31 4#usize)
  := do
  if group < 4#usize
  then
    let start ← 4#usize * group
    let q ← Array.index_usize state start
    let i ← start + 1#usize
    let q1 ← Array.index_usize state i
    let i1 ← start + 2#usize
    let q2 ← Array.index_usize state i1
    let i2 ← start + 3#usize
    let q3 ← Array.index_usize state i2
    let q4 ←
      state_only_poseidon.external_local_packed
        (Array.make 4#usize [ q, q1, q2, q3 ])
    let a ← Array.update local_packed group q4
    let group1 ← group + 1#usize
    state_only_poseidon.external_linear_packed_loop state a group1
  else ok local_packed
partial_fixpoint

/-- [aspis_r1_mask_extraction_probe::state_only_poseidon::external_linear_packed]:
    Source: 'src/statement/state_only_poseidon.rs', lines 285:0-305:1 -/
def state_only_poseidon.external_linear_packed
  (state : Array field.QM31 16#usize) : Result (Array field.QM31 4#usize) := do
  let local_packed := Array.repeat 4#usize field.QM31.ZERO
  let local_packed1 ←
    state_only_poseidon.external_linear_packed_loop state local_packed 0#usize
  let q ← Array.index_usize local_packed1 0#usize
  let q1 ← field.QM31.add field.QM31.ZERO q
  let q2 ← Array.index_usize local_packed1 1#usize
  let q3 ← field.QM31.add q1 q2
  let q4 ← Array.index_usize local_packed1 2#usize
  let q5 ← field.QM31.add q3 q4
  let q6 ← Array.index_usize local_packed1 3#usize
  let sum ← field.QM31.add q5 q6
  core.array.Array.map
    state_only_poseidon.external_linear_packed.closure.Insts.CoreOpsFunctionFnMutTupleQM31QM31
    local_packed1 sum

/-- [aspis_r1_mask_extraction_probe::state_only_poseidon::full_round_packed]: loop 0:
    Source: 'src/statement/state_only_poseidon.rs', lines 369:4-371:5 -/
@[rust_loop]
def state_only_poseidon.full_round_packed_loop
  (iter : core.ops.range.Range Std.Usize) (state : Array field.QM31 16#usize)
  (constants1 : Array field.QM31 16#usize) :
  Result (Array field.QM31 16#usize)
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok state
  | some lane =>
    let q ← Array.index_usize state lane
    let q1 ← Array.index_usize constants1 lane
    let q2 ← field.QM31.add q q1
    let q3 ← state_only_poseidon.pow5 q2
    let a ← Array.update state lane q3
    state_only_poseidon.full_round_packed_loop iter1 a constants1
partial_fixpoint

/-- [aspis_r1_mask_extraction_probe::state_only_poseidon::full_round_packed]:
    Source: 'src/statement/state_only_poseidon.rs', lines 365:0-373:1 -/
def state_only_poseidon.full_round_packed
  (state : Array field.QM31 16#usize) (constants1 : Array field.QM31 16#usize)
  :
  Result (Array field.QM31 4#usize)
  := do
  let state1 ←
    state_only_poseidon.full_round_packed_loop
      { start := 0#usize, «end» := poseidon2.POSEIDON2_WIDTH } state
      constants1
  state_only_poseidon.external_linear_packed state1


end FIq_Native
