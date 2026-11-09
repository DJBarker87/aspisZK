import RPu_FIq_FromFn
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.unusedVariables false
noncomputable section
namespace FIq_Native
/-- Trait implementation: [aspis_r1_mask_extraction_probe::state_only_poseidon::interpolated_internal_pair::{impl core::ops::function::FnOnce<(usize,), aspis_r1_mask_extraction_probe::field::M31> for aspis_r1_mask_extraction_probe::state_only_poseidon::interpolated_internal_pair::closure#1}]
    Source: 'src/statement/state_only_poseidon.rs', lines 535:34-535:68 -/
@[reducible]
def
  state_only_poseidon.interpolated_internal_pair.closure_1.Insts.CoreOpsFunctionFnOnceTupleUsizeM31
  : core.ops.function.FnOnce
  state_only_poseidon.interpolated_internal_pair.closure_1 Std.Usize field.M31
  := {
  call_once :=
    state_only_poseidon.interpolated_internal_pair.closure_1.Insts.CoreOpsFunctionFnOnceTupleUsizeM31.call_once
}

/-- Trait implementation: [aspis_r1_mask_extraction_probe::state_only_poseidon::interpolated_internal_pair::{impl core::ops::function::FnMut<(usize,), aspis_r1_mask_extraction_probe::field::M31> for aspis_r1_mask_extraction_probe::state_only_poseidon::interpolated_internal_pair::closure#1}]
    Source: 'src/statement/state_only_poseidon.rs', lines 535:34-535:68 -/
@[reducible]
def
  state_only_poseidon.interpolated_internal_pair.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeM31
  : core.ops.function.FnMut
  state_only_poseidon.interpolated_internal_pair.closure_1 Std.Usize field.M31
  := {
  FnOnceInst :=
    state_only_poseidon.interpolated_internal_pair.closure_1.Insts.CoreOpsFunctionFnOnceTupleUsizeM31
  call_mut :=
    state_only_poseidon.interpolated_internal_pair.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeM31.call_mut
}

/-- [aspis_r1_mask_extraction_probe::state_only_poseidon::interpolated_internal_pair::{impl core::ops::function::FnMut<(usize,), aspis_r1_mask_extraction_probe::field::QM31> for aspis_r1_mask_extraction_probe::state_only_poseidon::interpolated_internal_pair::closure<'_0>}::call_mut]:
    Source: 'src/statement/state_only_poseidon.rs', lines 534:27-534:43 -/
def
  state_only_poseidon.interpolated_internal_pair.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
  (c : state_only_poseidon.interpolated_internal_pair.closure)
  (tupled_args : Std.Usize) :
  Result (field.QM31 × state_only_poseidon.interpolated_internal_pair.closure)
  := do
  let q ← Array.index_usize c tupled_args
  ok (q, c)

/-- [aspis_r1_mask_extraction_probe::state_only_poseidon::interpolated_internal_pair::{impl core::ops::function::FnOnce<(usize,), aspis_r1_mask_extraction_probe::field::QM31> for aspis_r1_mask_extraction_probe::state_only_poseidon::interpolated_internal_pair::closure<'_0>}::call_once]:
    Source: 'src/statement/state_only_poseidon.rs', lines 534:27-534:43 -/
def
  state_only_poseidon.interpolated_internal_pair.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31.call_once
  (c : state_only_poseidon.interpolated_internal_pair.closure) (i : Std.Usize)
  :
  Result field.QM31
  := do
  let (q, _) ←
    state_only_poseidon.interpolated_internal_pair.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
      c i
  ok q

/-- Trait implementation: [aspis_r1_mask_extraction_probe::state_only_poseidon::interpolated_internal_pair::{impl core::ops::function::FnOnce<(usize,), aspis_r1_mask_extraction_probe::field::QM31> for aspis_r1_mask_extraction_probe::state_only_poseidon::interpolated_internal_pair::closure<'_0>}]
    Source: 'src/statement/state_only_poseidon.rs', lines 534:27-534:43 -/
@[reducible]
def
  state_only_poseidon.interpolated_internal_pair.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31
  : core.ops.function.FnOnce
  state_only_poseidon.interpolated_internal_pair.closure Std.Usize field.QM31
  := {
  call_once :=
    state_only_poseidon.interpolated_internal_pair.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31.call_once
}

/-- Trait implementation: [aspis_r1_mask_extraction_probe::state_only_poseidon::interpolated_internal_pair::{impl core::ops::function::FnMut<(usize,), aspis_r1_mask_extraction_probe::field::QM31> for aspis_r1_mask_extraction_probe::state_only_poseidon::interpolated_internal_pair::closure<'_0>}]
    Source: 'src/statement/state_only_poseidon.rs', lines 534:27-534:43 -/
@[reducible]
def
  state_only_poseidon.interpolated_internal_pair.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31
  : core.ops.function.FnMut
  state_only_poseidon.interpolated_internal_pair.closure Std.Usize field.QM31
  := {
  FnOnceInst :=
    state_only_poseidon.interpolated_internal_pair.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31
  call_mut :=
    state_only_poseidon.interpolated_internal_pair.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
}

/-- [aspis_r1_mask_extraction_probe::state_only_poseidon::interpolated_internal_pair::ROWS]
    Source: 'src/statement/state_only_poseidon.rs', lines 533:4-533:51 -/
@[global_simps, irreducible]
def state_only_poseidon.interpolated_internal_pair.ROWS
  : Array Std.Usize 7#usize :=
  Array.make 7#usize [
    2#usize, 3#usize, 4#usize, 5#usize, 6#usize, 7#usize, 8#usize
    ]

/-- [aspis_r1_mask_extraction_probe::state_only_poseidon::internal_linear_lazy::SHIFTS]
    Source: 'src/statement/state_only_poseidon.rs', lines 309:4-309:81 -/
@[global_simps, irreducible]
def state_only_poseidon.internal_linear_lazy.SHIFTS : Array Std.U8 15#usize :=
  Array.make 15#usize [
    0#u8, 1#u8, 2#u8, 3#u8, 4#u8, 5#u8, 6#u8, 7#u8, 8#u8, 10#u8, 12#u8, 13#u8,
    14#u8, 15#u8, 16#u8
    ]

/-- [aspis_r1_mask_extraction_probe::state_only_poseidon::internal_linear_lazy::{impl core::ops::function::FnMut<(usize,), u64> for aspis_r1_mask_extraction_probe::state_only_poseidon::internal_linear_lazy::closure#2<'_0, '_1, '_2>}::call_mut]:
    Source: 'src/statement/state_only_poseidon.rs', lines 330:87-332:9 -/
def
  state_only_poseidon.internal_linear_lazy.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeU64.call_mut
  (c : state_only_poseidon.internal_linear_lazy.closure_2)
  (tupled_args : Std.Usize) :
  Result (Std.U64 × state_only_poseidon.internal_linear_lazy.closure_2)
  := do
  let (a, a1, i) := c
  let i1 ← Array.index_usize a tupled_args
  let i2 ← Array.index_usize a1 tupled_args
  let i3 ← lift (core.convert.num.FromU64U32.from i2)
  let i4 ← i - 1#usize
  let i5 ←
    Array.index_usize state_only_poseidon.internal_linear_lazy.SHIFTS i4
  let i6 ← i3 <<< i5
  let i7 ← i1 + i6
  ok (i7, c)

/-- [aspis_r1_mask_extraction_probe::state_only_poseidon::internal_linear_lazy::{impl core::ops::function::FnOnce<(usize,), u64> for aspis_r1_mask_extraction_probe::state_only_poseidon::internal_linear_lazy::closure#2<'_0, '_1, '_2>}::call_once]:
    Source: 'src/statement/state_only_poseidon.rs', lines 330:87-332:9 -/
def
  state_only_poseidon.internal_linear_lazy.closure_2.Insts.CoreOpsFunctionFnOnceTupleUsizeU64.call_once
  (c : state_only_poseidon.internal_linear_lazy.closure_2) (i : Std.Usize) :
  Result Std.U64
  := do
  let (i1, _) ←
    state_only_poseidon.internal_linear_lazy.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeU64.call_mut
      c i
  ok i1

/-- Trait implementation: [aspis_r1_mask_extraction_probe::state_only_poseidon::internal_linear_lazy::{impl core::ops::function::FnOnce<(usize,), u64> for aspis_r1_mask_extraction_probe::state_only_poseidon::internal_linear_lazy::closure#2<'_0, '_1, '_2>}]
    Source: 'src/statement/state_only_poseidon.rs', lines 330:87-332:9 -/
@[reducible]
def
  state_only_poseidon.internal_linear_lazy.closure_2.Insts.CoreOpsFunctionFnOnceTupleUsizeU64
  : core.ops.function.FnOnce state_only_poseidon.internal_linear_lazy.closure_2
  Std.Usize Std.U64 := {
  call_once :=
    state_only_poseidon.internal_linear_lazy.closure_2.Insts.CoreOpsFunctionFnOnceTupleUsizeU64.call_once
}

/-- Trait implementation: [aspis_r1_mask_extraction_probe::state_only_poseidon::internal_linear_lazy::{impl core::ops::function::FnMut<(usize,), u64> for aspis_r1_mask_extraction_probe::state_only_poseidon::internal_linear_lazy::closure#2<'_0, '_1, '_2>}]
    Source: 'src/statement/state_only_poseidon.rs', lines 330:87-332:9 -/
@[reducible]
def
  state_only_poseidon.internal_linear_lazy.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeU64
  : core.ops.function.FnMut state_only_poseidon.internal_linear_lazy.closure_2
  Std.Usize Std.U64 := {
  FnOnceInst :=
    state_only_poseidon.internal_linear_lazy.closure_2.Insts.CoreOpsFunctionFnOnceTupleUsizeU64
  call_mut :=
    state_only_poseidon.internal_linear_lazy.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeU64.call_mut
}

/-- [aspis_r1_mask_extraction_probe::state_only_poseidon::internal_linear_lazy::{impl core::ops::function::FnMut<(usize,), u64> for aspis_r1_mask_extraction_probe::state_only_poseidon::internal_linear_lazy::closure#1<'_0, '_1>}::call_mut]:
    Source: 'src/statement/state_only_poseidon.rs', lines 325:80-327:5 -/
def
  state_only_poseidon.internal_linear_lazy.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeU64.call_mut
  (c : state_only_poseidon.internal_linear_lazy.closure_1)
  (tupled_args : Std.Usize) :
  Result (Std.U64 × state_only_poseidon.internal_linear_lazy.closure_1)
  := do
  let (a, a1) := c
  let i ← Array.index_usize a tupled_args
  let i1 ← lift (core.convert.num.FromU64U32.from field.P)
  let i2 ← i + i1
  let i3 ← Array.index_usize a1 tupled_args
  let i4 ← lift (core.convert.num.FromU64U32.from i3)
  let i5 ← i2 - i4
  ok (i5, c)

/-- [aspis_r1_mask_extraction_probe::state_only_poseidon::internal_linear_lazy::{impl core::ops::function::FnOnce<(usize,), u64> for aspis_r1_mask_extraction_probe::state_only_poseidon::internal_linear_lazy::closure#1<'_0, '_1>}::call_once]:
    Source: 'src/statement/state_only_poseidon.rs', lines 325:80-327:5 -/
def
  state_only_poseidon.internal_linear_lazy.closure_1.Insts.CoreOpsFunctionFnOnceTupleUsizeU64.call_once
  (c : state_only_poseidon.internal_linear_lazy.closure_1) (i : Std.Usize) :
  Result Std.U64
  := do
  let (i1, _) ←
    state_only_poseidon.internal_linear_lazy.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeU64.call_mut
      c i
  ok i1

/-- Trait implementation: [aspis_r1_mask_extraction_probe::state_only_poseidon::internal_linear_lazy::{impl core::ops::function::FnOnce<(usize,), u64> for aspis_r1_mask_extraction_probe::state_only_poseidon::internal_linear_lazy::closure#1<'_0, '_1>}]
    Source: 'src/statement/state_only_poseidon.rs', lines 325:80-327:5 -/
@[reducible]
def
  state_only_poseidon.internal_linear_lazy.closure_1.Insts.CoreOpsFunctionFnOnceTupleUsizeU64
  : core.ops.function.FnOnce state_only_poseidon.internal_linear_lazy.closure_1
  Std.Usize Std.U64 := {
  call_once :=
    state_only_poseidon.internal_linear_lazy.closure_1.Insts.CoreOpsFunctionFnOnceTupleUsizeU64.call_once
}

/-- Trait implementation: [aspis_r1_mask_extraction_probe::state_only_poseidon::internal_linear_lazy::{impl core::ops::function::FnMut<(usize,), u64> for aspis_r1_mask_extraction_probe::state_only_poseidon::internal_linear_lazy::closure#1<'_0, '_1>}]
    Source: 'src/statement/state_only_poseidon.rs', lines 325:80-327:5 -/
@[reducible]
def
  state_only_poseidon.internal_linear_lazy.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeU64
  : core.ops.function.FnMut state_only_poseidon.internal_linear_lazy.closure_1
  Std.Usize Std.U64 := {
  FnOnceInst :=
    state_only_poseidon.internal_linear_lazy.closure_1.Insts.CoreOpsFunctionFnOnceTupleUsizeU64
  call_mut :=
    state_only_poseidon.internal_linear_lazy.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeU64.call_mut
}

/-- [aspis_r1_mask_extraction_probe::state_only_poseidon::internal_linear_lazy::{impl core::ops::function::FnMut<(usize,), u64> for aspis_r1_mask_extraction_probe::state_only_poseidon::internal_linear_lazy::closure<'_0, '_1>}::call_mut]:
    Source: 'src/statement/state_only_poseidon.rs', lines 322:69-324:5 -/
def
  state_only_poseidon.internal_linear_lazy.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64.call_mut
  (c : state_only_poseidon.internal_linear_lazy.closure)
  (tupled_args : Std.Usize) :
  Result (Std.U64 × state_only_poseidon.internal_linear_lazy.closure)
  := do
  let (a, a1) := c
  let i ← Array.index_usize a tupled_args
  let i1 ← Array.index_usize a1 tupled_args
  let i2 ← lift (core.convert.num.FromU64U32.from i1)
  let i3 ← i + i2
  ok (i3, c)

/-- [aspis_r1_mask_extraction_probe::state_only_poseidon::internal_linear_lazy::{impl core::ops::function::FnOnce<(usize,), u64> for aspis_r1_mask_extraction_probe::state_only_poseidon::internal_linear_lazy::closure<'_0, '_1>}::call_once]:
    Source: 'src/statement/state_only_poseidon.rs', lines 322:69-324:5 -/
def
  state_only_poseidon.internal_linear_lazy.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeU64.call_once
  (c : state_only_poseidon.internal_linear_lazy.closure) (i : Std.Usize) :
  Result Std.U64
  := do
  let (i1, _) ←
    state_only_poseidon.internal_linear_lazy.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64.call_mut
      c i
  ok i1

/-- Trait implementation: [aspis_r1_mask_extraction_probe::state_only_poseidon::internal_linear_lazy::{impl core::ops::function::FnOnce<(usize,), u64> for aspis_r1_mask_extraction_probe::state_only_poseidon::internal_linear_lazy::closure<'_0, '_1>}]
    Source: 'src/statement/state_only_poseidon.rs', lines 322:69-324:5 -/
@[reducible]
def
  state_only_poseidon.internal_linear_lazy.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeU64
  : core.ops.function.FnOnce state_only_poseidon.internal_linear_lazy.closure
  Std.Usize Std.U64 := {
  call_once :=
    state_only_poseidon.internal_linear_lazy.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeU64.call_once
}

/-- Trait implementation: [aspis_r1_mask_extraction_probe::state_only_poseidon::internal_linear_lazy::{impl core::ops::function::FnMut<(usize,), u64> for aspis_r1_mask_extraction_probe::state_only_poseidon::internal_linear_lazy::closure<'_0, '_1>}]
    Source: 'src/statement/state_only_poseidon.rs', lines 322:69-324:5 -/
@[reducible]
def
  state_only_poseidon.internal_linear_lazy.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64
  : core.ops.function.FnMut state_only_poseidon.internal_linear_lazy.closure
  Std.Usize Std.U64 := {
  FnOnceInst :=
    state_only_poseidon.internal_linear_lazy.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeU64
  call_mut :=
    state_only_poseidon.internal_linear_lazy.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64.call_mut
}

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

/-- [aspis_r1_mask_extraction_probe::poseidon2::POSEIDON2_WIDTH]
    Source: 'src/statement/poseidon2.rs', lines 56:0-56:38
    Visibility: public -/
@[global_simps, irreducible]
def poseidon2.POSEIDON2_WIDTH : Std.Usize := 16#usize

/-- [aspis_r1_mask_extraction_probe::state_only_poseidon::internal_linear_lazy]: loop 1:
    Source: 'src/statement/state_only_poseidon.rs', lines 316:8-319:9 -/
@[rust_loop]
def state_only_poseidon.internal_linear_lazy_loop0_loop0
  (part_sum : Array Std.U64 4#usize) (limbs : Array Std.U32 4#usize)
  (limb : Std.Usize) :
  Result (Array Std.U64 4#usize)
  := do
  if limb < 4#usize
  then
    let i ← Array.index_usize limbs limb
    let i1 ← lift (core.convert.num.FromU64U32.from i)
    let i2 ← Array.index_usize part_sum limb
    let i3 ← i2 + i1
    let a ← Array.update part_sum limb i3
    let limb1 ← limb + 1#usize
    state_only_poseidon.internal_linear_lazy_loop0_loop0 a limbs limb1
  else ok part_sum
partial_fixpoint

/-- [aspis_r1_mask_extraction_probe::state_only_poseidon::internal_linear_lazy]: loop 0:
    Source: 'src/statement/state_only_poseidon.rs', lines 313:4-321:5 -/
@[rust_loop]
def state_only_poseidon.internal_linear_lazy_loop0
  (state : Array field.QM31 16#usize) (part_sum : Array Std.U64 4#usize)
  (lane : Std.Usize) :
  Result (Array Std.U64 4#usize)
  := do
  if lane < poseidon2.POSEIDON2_WIDTH
  then
    let q ← Array.index_usize state lane
    let limbs ← state_only_poseidon.extension_limbs q
    let part_sum1 ←
      state_only_poseidon.internal_linear_lazy_loop0_loop0 part_sum limbs
        0#usize
    let lane1 ← lane + 1#usize
    state_only_poseidon.internal_linear_lazy_loop0 state part_sum1 lane1
  else ok part_sum
partial_fixpoint

/-- [aspis_r1_mask_extraction_probe::state_only_poseidon::internal_linear_lazy]: loop 2:
    Source: 'src/statement/state_only_poseidon.rs', lines 328:4-333:5 -/
@[rust_loop]
def state_only_poseidon.internal_linear_lazy_loop1
  (iter : core.ops.range.Range Std.Usize) (state : Array field.QM31 16#usize)
  (full_sum : Array Std.U64 4#usize) :
  Result (Array field.QM31 16#usize)
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok state
  | some lane =>
    let q ← Array.index_usize state lane
    let limbs ← state_only_poseidon.extension_limbs q
    let a ←
      array_from_fn_copy 4#usize core.marker.CopyU64
        state_only_poseidon.internal_linear_lazy.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeU64
        0#u64 (full_sum, limbs, lane)
    let q1 ← state_only_poseidon.extension_from_raw_limbs a
    let a1 ← Array.update state lane q1
    state_only_poseidon.internal_linear_lazy_loop1 iter1 a1 full_sum
partial_fixpoint

/-- [aspis_r1_mask_extraction_probe::state_only_poseidon::internal_linear_lazy]:
    Source: 'src/statement/state_only_poseidon.rs', lines 308:0-334:1 -/
def state_only_poseidon.internal_linear_lazy
  (state : Array field.QM31 16#usize) :
  Result (Array field.QM31 16#usize)
  := do
  let q ← Array.index_usize state 0#usize
  let old_zero ← state_only_poseidon.extension_limbs q
  let part_sum := Array.repeat 4#usize 0#u64
  let part_sum1 ←
    state_only_poseidon.internal_linear_lazy_loop0 state part_sum 1#usize
  let full_sum ←
    array_from_fn_copy 4#usize core.marker.CopyU64
      state_only_poseidon.internal_linear_lazy.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64
      0#u64 (part_sum1, old_zero)
  let a ←
    array_from_fn_copy 4#usize core.marker.CopyU64
      state_only_poseidon.internal_linear_lazy.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeU64
      0#u64 (part_sum1, old_zero)
  let q1 ← state_only_poseidon.extension_from_raw_limbs a
  let a1 ← Array.update state 0#usize q1
  state_only_poseidon.internal_linear_lazy_loop1
    { start := 1#usize, «end» := poseidon2.POSEIDON2_WIDTH } a1 full_sum

/-- [aspis_r1_mask_extraction_probe::state_only_poseidon::pow5]:
    Source: 'src/statement/state_only_poseidon.rs', lines 124:0-127:1 -/
def state_only_poseidon.pow5 (value : field.QM31) : Result field.QM31 := do
  let square ← field.QM31.square value
  let q ← field.QM31.square square
  field.QM31.mul q value

/-- [aspis_r1_mask_extraction_probe::state_only_poseidon::internal_round]:
    Source: 'src/statement/state_only_poseidon.rs', lines 388:0-392:1 -/
def state_only_poseidon.internal_round
  (state : Array field.QM31 16#usize) (constant1 : field.QM31) :
  Result (Array field.QM31 16#usize)
  := do
  let q ← Array.index_usize state 0#usize
  let q1 ← field.QM31.add q constant1
  let q2 ← state_only_poseidon.pow5 q1
  let state1 ← Array.update state 0#usize q2
  state_only_poseidon.internal_linear_lazy state1

/-- [aspis_r1_mask_extraction_probe::state_only_poseidon::interpolated_internal_pair]:
    Source: 'src/statement/state_only_poseidon.rs', lines 529:0-540:1 -/
def state_only_poseidon.interpolated_internal_pair
  (state : Array field.QM31 16#usize) (local1 : Array field.QM31 16#usize) :
  Result (Array field.QM31 16#usize)
  := do
  let weights ←
    core.array.Array.map
      state_only_poseidon.interpolated_internal_pair.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31
      state_only_poseidon.interpolated_internal_pair.ROWS local1
  let even_constants ←
    core.array.Array.map
      state_only_poseidon.interpolated_internal_pair.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeM31
      state_only_poseidon.interpolated_internal_pair.ROWS ()
  let odd_constants ←
    core.array.Array.map
      state_only_poseidon.interpolated_internal_pair.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeM31
      state_only_poseidon.interpolated_internal_pair.ROWS ()
  let s ← lift (Array.to_slice weights)
  let s1 ← lift (Array.to_slice even_constants)
  let even ← field.qm31_m31_dot s s1
  let s2 ← lift (Array.to_slice weights)
  let s3 ← lift (Array.to_slice odd_constants)
  let odd ← field.qm31_m31_dot s2 s3
  let a ← state_only_poseidon.internal_round state even
  state_only_poseidon.internal_round a odd


end FIq_Native
