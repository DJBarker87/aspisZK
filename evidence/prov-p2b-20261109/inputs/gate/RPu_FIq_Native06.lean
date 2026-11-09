import RPu_FIq_Native05
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.unusedVariables false
noncomputable section
namespace FIq_Native
/-- [aspis_r1_mask_extraction_probe::state_only_poseidon::external_linear_lazy::{impl core::ops::function::FnMut<(usize,), u64> for aspis_r1_mask_extraction_probe::state_only_poseidon::external_linear_lazy::closure#1<'_0, '_1, '_2>}::call_mut]:
    Source: 'src/statement/state_only_poseidon.rs', lines 190:88-192:9 -/
def
  state_only_poseidon.external_linear_lazy.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeU64.call_mut
  (c : state_only_poseidon.external_linear_lazy.closure_1)
  (tupled_args : Std.Usize) :
  Result (Std.U64 × state_only_poseidon.external_linear_lazy.closure_1)
  := do
  let (a, a1, i) := c
  let i1 ← Array.index_usize a tupled_args
  let i2 ← lift (core.convert.num.FromU64U32.from i1)
  let i3 ← lift (i &&& 3#usize)
  let a2 ← Array.index_usize a1 i3
  let i4 ← Array.index_usize a2 tupled_args
  let i5 ← i2 + i4
  ok (i5, c)

/-- [aspis_r1_mask_extraction_probe::state_only_poseidon::external_linear_lazy::{impl core::ops::function::FnOnce<(usize,), u64> for aspis_r1_mask_extraction_probe::state_only_poseidon::external_linear_lazy::closure#1<'_0, '_1, '_2>}::call_once]:
    Source: 'src/statement/state_only_poseidon.rs', lines 190:88-192:9 -/
def
  state_only_poseidon.external_linear_lazy.closure_1.Insts.CoreOpsFunctionFnOnceTupleUsizeU64.call_once
  (c : state_only_poseidon.external_linear_lazy.closure_1) (i : Std.Usize) :
  Result Std.U64
  := do
  let (i1, _) ←
    state_only_poseidon.external_linear_lazy.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeU64.call_mut
      c i
  ok i1

/-- Trait implementation: [aspis_r1_mask_extraction_probe::state_only_poseidon::external_linear_lazy::{impl core::ops::function::FnOnce<(usize,), u64> for aspis_r1_mask_extraction_probe::state_only_poseidon::external_linear_lazy::closure#1<'_0, '_1, '_2>}]
    Source: 'src/statement/state_only_poseidon.rs', lines 190:88-192:9 -/
@[reducible]
def
  state_only_poseidon.external_linear_lazy.closure_1.Insts.CoreOpsFunctionFnOnceTupleUsizeU64
  : core.ops.function.FnOnce state_only_poseidon.external_linear_lazy.closure_1
  Std.Usize Std.U64 := {
  call_once :=
    state_only_poseidon.external_linear_lazy.closure_1.Insts.CoreOpsFunctionFnOnceTupleUsizeU64.call_once
}

/-- Trait implementation: [aspis_r1_mask_extraction_probe::state_only_poseidon::external_linear_lazy::{impl core::ops::function::FnMut<(usize,), u64> for aspis_r1_mask_extraction_probe::state_only_poseidon::external_linear_lazy::closure#1<'_0, '_1, '_2>}]
    Source: 'src/statement/state_only_poseidon.rs', lines 190:88-192:9 -/
@[reducible]
def
  state_only_poseidon.external_linear_lazy.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeU64
  : core.ops.function.FnMut state_only_poseidon.external_linear_lazy.closure_1
  Std.Usize Std.U64 := {
  FnOnceInst :=
    state_only_poseidon.external_linear_lazy.closure_1.Insts.CoreOpsFunctionFnOnceTupleUsizeU64
  call_mut :=
    state_only_poseidon.external_linear_lazy.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeU64.call_mut
}

/-- [aspis_r1_mask_extraction_probe::state_only_poseidon::external_linear_lazy::closure::{impl core::ops::function::FnMut<(usize,), u64> for aspis_r1_mask_extraction_probe::state_only_poseidon::external_linear_lazy::closure::closure<'_0, '_1>}::call_mut]:
    Source: 'src/statement/state_only_poseidon.rs', lines 180:48-185:9 -/
def
  state_only_poseidon.external_linear_lazy.closure.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64.call_mut
  (c : state_only_poseidon.external_linear_lazy.closure.closure)
  (tupled_args : Std.Usize) :
  Result (Std.U64 × state_only_poseidon.external_linear_lazy.closure.closure)
  := do
  let (a, i) := c
  let q ← Array.index_usize a i
  let a1 ← state_only_poseidon.extension_limbs q
  let i1 ← Array.index_usize a1 tupled_args
  let i2 ← lift (core.convert.num.FromU64U32.from i1)
  let i3 ← 4#usize + i
  let q1 ← Array.index_usize a i3
  let a2 ← state_only_poseidon.extension_limbs q1
  let i4 ← Array.index_usize a2 tupled_args
  let i5 ← lift (core.convert.num.FromU64U32.from i4)
  let i6 ← i2 + i5
  let i7 ← 8#usize + i
  let q2 ← Array.index_usize a i7
  let a3 ← state_only_poseidon.extension_limbs q2
  let i8 ← Array.index_usize a3 tupled_args
  let i9 ← lift (core.convert.num.FromU64U32.from i8)
  let i10 ← i6 + i9
  let i11 ← 12#usize + i
  let q3 ← Array.index_usize a i11
  let a4 ← state_only_poseidon.extension_limbs q3
  let i12 ← Array.index_usize a4 tupled_args
  let i13 ← lift (core.convert.num.FromU64U32.from i12)
  let i14 ← i10 + i13
  ok (i14, c)

/-- [aspis_r1_mask_extraction_probe::state_only_poseidon::external_linear_lazy::closure::{impl core::ops::function::FnOnce<(usize,), u64> for aspis_r1_mask_extraction_probe::state_only_poseidon::external_linear_lazy::closure::closure<'_0, '_1>}::call_once]:
    Source: 'src/statement/state_only_poseidon.rs', lines 180:48-185:9 -/
def
  state_only_poseidon.external_linear_lazy.closure.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeU64.call_once
  (c : state_only_poseidon.external_linear_lazy.closure.closure)
  (i : Std.Usize) :
  Result Std.U64
  := do
  let (i1, _) ←
    state_only_poseidon.external_linear_lazy.closure.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64.call_mut
      c i
  ok i1

/-- Trait implementation: [aspis_r1_mask_extraction_probe::state_only_poseidon::external_linear_lazy::closure::{impl core::ops::function::FnOnce<(usize,), u64> for aspis_r1_mask_extraction_probe::state_only_poseidon::external_linear_lazy::closure::closure<'_0, '_1>}]
    Source: 'src/statement/state_only_poseidon.rs', lines 180:48-185:9 -/
@[reducible]
def
  state_only_poseidon.external_linear_lazy.closure.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeU64
  : core.ops.function.FnOnce
  state_only_poseidon.external_linear_lazy.closure.closure Std.Usize Std.U64
  := {
  call_once :=
    state_only_poseidon.external_linear_lazy.closure.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeU64.call_once
}

/-- Trait implementation: [aspis_r1_mask_extraction_probe::state_only_poseidon::external_linear_lazy::closure::{impl core::ops::function::FnMut<(usize,), u64> for aspis_r1_mask_extraction_probe::state_only_poseidon::external_linear_lazy::closure::closure<'_0, '_1>}]
    Source: 'src/statement/state_only_poseidon.rs', lines 180:48-185:9 -/
@[reducible]
def
  state_only_poseidon.external_linear_lazy.closure.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64
  : core.ops.function.FnMut
  state_only_poseidon.external_linear_lazy.closure.closure Std.Usize Std.U64
  := {
  FnOnceInst :=
    state_only_poseidon.external_linear_lazy.closure.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeU64
  call_mut :=
    state_only_poseidon.external_linear_lazy.closure.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64.call_mut
}

/-- [aspis_r1_mask_extraction_probe::state_only_poseidon::external_linear_lazy::{impl core::ops::function::FnMut<(usize,), [u64; 4usize]> for aspis_r1_mask_extraction_probe::state_only_poseidon::external_linear_lazy::closure<'_0>}::call_mut]:
    Source: 'src/statement/state_only_poseidon.rs', lines 179:75-186:5 -/
def
  state_only_poseidon.external_linear_lazy.closure.Insts.CoreOpsFunctionFnMutTupleUsizeArrayU644.call_mut
  (c : state_only_poseidon.external_linear_lazy.closure)
  (tupled_args : Std.Usize) :
  Result ((Array Std.U64 4#usize) ×
    state_only_poseidon.external_linear_lazy.closure)
  := do
  let a ←
    array_from_fn_copy 4#usize core.marker.CopyU64
      state_only_poseidon.external_linear_lazy.closure.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64
      0#u64 (c, tupled_args)
  ok (a, c)

/-- [aspis_r1_mask_extraction_probe::state_only_poseidon::external_linear_lazy::{impl core::ops::function::FnOnce<(usize,), [u64; 4usize]> for aspis_r1_mask_extraction_probe::state_only_poseidon::external_linear_lazy::closure<'_0>}::call_once]:
    Source: 'src/statement/state_only_poseidon.rs', lines 179:75-186:5 -/
def
  state_only_poseidon.external_linear_lazy.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeArrayU644.call_once
  (c : state_only_poseidon.external_linear_lazy.closure) (i : Std.Usize) :
  Result (Array Std.U64 4#usize)
  := do
  let (a, _) ←
    state_only_poseidon.external_linear_lazy.closure.Insts.CoreOpsFunctionFnMutTupleUsizeArrayU644.call_mut
      c i
  ok a

/-- Trait implementation: [aspis_r1_mask_extraction_probe::state_only_poseidon::external_linear_lazy::{impl core::ops::function::FnOnce<(usize,), [u64; 4usize]> for aspis_r1_mask_extraction_probe::state_only_poseidon::external_linear_lazy::closure<'_0>}]
    Source: 'src/statement/state_only_poseidon.rs', lines 179:75-186:5 -/
@[reducible]
def
  state_only_poseidon.external_linear_lazy.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeArrayU644
  : core.ops.function.FnOnce state_only_poseidon.external_linear_lazy.closure
  Std.Usize (Array Std.U64 4#usize) := {
  call_once :=
    state_only_poseidon.external_linear_lazy.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeArrayU644.call_once
}

/-- Trait implementation: [aspis_r1_mask_extraction_probe::state_only_poseidon::external_linear_lazy::{impl core::ops::function::FnMut<(usize,), [u64; 4usize]> for aspis_r1_mask_extraction_probe::state_only_poseidon::external_linear_lazy::closure<'_0>}]
    Source: 'src/statement/state_only_poseidon.rs', lines 179:75-186:5 -/
@[reducible]
def
  state_only_poseidon.external_linear_lazy.closure.Insts.CoreOpsFunctionFnMutTupleUsizeArrayU644
  : core.ops.function.FnMut state_only_poseidon.external_linear_lazy.closure
  Std.Usize (Array Std.U64 4#usize) := {
  FnOnceInst :=
    state_only_poseidon.external_linear_lazy.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeArrayU644
  call_mut :=
    state_only_poseidon.external_linear_lazy.closure.Insts.CoreOpsFunctionFnMutTupleUsizeArrayU644.call_mut
}

/-- [aspis_r1_mask_extraction_probe::state_only_poseidon::external_linear_lazy_row::{impl core::ops::function::FnMut<(usize,), u64> for aspis_r1_mask_extraction_probe::state_only_poseidon::external_linear_lazy_row::closure<'_0, '_1>}::call_mut]:
    Source: 'src/statement/state_only_poseidon.rs', lines 144:54-156:5 -/
def
  state_only_poseidon.external_linear_lazy_row.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64.call_mut
  (c : state_only_poseidon.external_linear_lazy_row.closure)
  (tupled_args : Std.Usize) :
  Result (Std.U64 × state_only_poseidon.external_linear_lazy_row.closure)
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

/-- [aspis_r1_mask_extraction_probe::state_only_poseidon::external_linear_lazy_row::{impl core::ops::function::FnOnce<(usize,), u64> for aspis_r1_mask_extraction_probe::state_only_poseidon::external_linear_lazy_row::closure<'_0, '_1>}::call_once]:
    Source: 'src/statement/state_only_poseidon.rs', lines 144:54-156:5 -/
def
  state_only_poseidon.external_linear_lazy_row.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeU64.call_once
  (c : state_only_poseidon.external_linear_lazy_row.closure) (i : Std.Usize) :
  Result Std.U64
  := do
  let (i1, _) ←
    state_only_poseidon.external_linear_lazy_row.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64.call_mut
      c i
  ok i1

/-- Trait implementation: [aspis_r1_mask_extraction_probe::state_only_poseidon::external_linear_lazy_row::{impl core::ops::function::FnOnce<(usize,), u64> for aspis_r1_mask_extraction_probe::state_only_poseidon::external_linear_lazy_row::closure<'_0, '_1>}]
    Source: 'src/statement/state_only_poseidon.rs', lines 144:54-156:5 -/
@[reducible]
def
  state_only_poseidon.external_linear_lazy_row.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeU64
  : core.ops.function.FnOnce
  state_only_poseidon.external_linear_lazy_row.closure Std.Usize Std.U64 := {
  call_once :=
    state_only_poseidon.external_linear_lazy_row.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeU64.call_once
}

/-- Trait implementation: [aspis_r1_mask_extraction_probe::state_only_poseidon::external_linear_lazy_row::{impl core::ops::function::FnMut<(usize,), u64> for aspis_r1_mask_extraction_probe::state_only_poseidon::external_linear_lazy_row::closure<'_0, '_1>}]
    Source: 'src/statement/state_only_poseidon.rs', lines 144:54-156:5 -/
@[reducible]
def
  state_only_poseidon.external_linear_lazy_row.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64
  : core.ops.function.FnMut
  state_only_poseidon.external_linear_lazy_row.closure Std.Usize Std.U64 := {
  FnOnceInst :=
    state_only_poseidon.external_linear_lazy_row.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeU64
  call_mut :=
    state_only_poseidon.external_linear_lazy_row.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64.call_mut
}

/-- [aspis_r1_mask_extraction_probe::state_only_poseidon::external_linear_lazy_row]:
    Source: 'src/statement/state_only_poseidon.rs', lines 143:0-158:1 -/
def state_only_poseidon.external_linear_lazy_row
  (input : Array (Array Std.U32 4#usize) 4#usize) (output : Std.Usize) :
  Result field.QM31
  := do
  let raw1 ←
    array_from_fn_copy 4#usize core.marker.CopyU64
      state_only_poseidon.external_linear_lazy_row.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64
      0#u64 (input, output)
  state_only_poseidon.extension_from_raw_limbs raw1

/-- [aspis_r1_mask_extraction_probe::state_only_poseidon::external_linear_lazy]: loop 0:
    Source: 'src/statement/state_only_poseidon.rs', lines 164:4-178:5 -/
@[rust_loop]
def state_only_poseidon.external_linear_lazy_loop0
  (state : Array field.QM31 16#usize) (group : Std.Usize) :
  Result (Array field.QM31 16#usize)
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
    let input ←
      core.array.Array.map (BuiltinFnMut field.QM31 (Array Std.U32 4#usize))
        (Array.make 4#usize [ q, q1, q2, q3 ])
        (state_only_poseidon.extension_limbs)
    let q4 ← state_only_poseidon.external_linear_lazy_row input 0#usize
    let state1 ← Array.update state start q4
    let q5 ← state_only_poseidon.external_linear_lazy_row input 1#usize
    let state2 ← Array.update state1 i q5
    let q6 ← state_only_poseidon.external_linear_lazy_row input 2#usize
    let state3 ← Array.update state2 i1 q6
    let q7 ← state_only_poseidon.external_linear_lazy_row input 3#usize
    let a ← Array.update state3 i2 q7
    let group1 ← group + 1#usize
    state_only_poseidon.external_linear_lazy_loop0 a group1
  else ok state
partial_fixpoint

/-- [aspis_r1_mask_extraction_probe::state_only_poseidon::external_linear_lazy]: loop 1:
    Source: 'src/statement/state_only_poseidon.rs', lines 188:4-194:5 -/
@[rust_loop]
def state_only_poseidon.external_linear_lazy_loop1
  (state : Array field.QM31 16#usize)
  (sums : Array (Array Std.U64 4#usize) 4#usize) (index : Std.Usize) :
  Result (Array field.QM31 16#usize)
  := do
  if index < poseidon2.POSEIDON2_WIDTH
  then
    let q ← Array.index_usize state index
    let limbs ← state_only_poseidon.extension_limbs q
    let a ←
      array_from_fn_copy 4#usize core.marker.CopyU64
        state_only_poseidon.external_linear_lazy.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeU64
        0#u64 (limbs, sums, index)
    let q1 ← state_only_poseidon.extension_from_raw_limbs a
    let a1 ← Array.update state index q1
    let index1 ← index + 1#usize
    state_only_poseidon.external_linear_lazy_loop1 a1 sums index1
  else ok state
partial_fixpoint

/-- [aspis_r1_mask_extraction_probe::state_only_poseidon::external_linear_lazy]:
    Source: 'src/statement/state_only_poseidon.rs', lines 162:0-195:1 -/
def state_only_poseidon.external_linear_lazy
  (state : Array field.QM31 16#usize) :
  Result (Array field.QM31 16#usize)
  := do
  let state1 ← state_only_poseidon.external_linear_lazy_loop0 state 0#usize
  let a := Array.repeat 4#usize 0#u64
  let sums ←
    array_from_fn_copy 4#usize (Array.Insts.CoreMarkerCopy 4#usize
      core.marker.CopyU64)
      state_only_poseidon.external_linear_lazy.closure.Insts.CoreOpsFunctionFnMutTupleUsizeArrayU644
      a state1
  state_only_poseidon.external_linear_lazy_loop1 state1 sums 0#usize

/-- [aspis_r1_mask_extraction_probe::state_only_poseidon::full_round]: loop 0:
    Source: 'src/statement/state_only_poseidon.rs', lines 341:4-343:5 -/
@[rust_loop]
def state_only_poseidon.full_round_loop
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
    state_only_poseidon.full_round_loop iter1 a constants1
partial_fixpoint

/-- [aspis_r1_mask_extraction_probe::state_only_poseidon::full_round]:
    Source: 'src/statement/state_only_poseidon.rs', lines 337:0-346:1 -/
def state_only_poseidon.full_round
  (state : Array field.QM31 16#usize) (constants1 : Array field.QM31 16#usize)
  :
  Result (Array field.QM31 16#usize)
  := do
  let state1 ←
    state_only_poseidon.full_round_loop
      { start := 0#usize, «end» := poseidon2.POSEIDON2_WIDTH } state
      constants1
  state_only_poseidon.external_linear_lazy state1

/-- [aspis_r1_mask_extraction_probe::poseidon2::EXTERNAL_FINAL]
    Source: 'src/statement/poseidon2.rs', lines 106:0-127:2 -/
@[global_simps, irreducible]
def poseidon2.EXTERNAL_FINAL : Array (Array Std.U32 16#usize) 4#usize :=
  Array.make 4#usize [
    Array.make 16#usize [
      1460209171#u32, 530850056#u32, 398192464#u32, 536338716#u32,
      75179210#u32, 1309934197#u32, 1335920373#u32, 127611036#u32,
      291093831#u32, 1832379621#u32, 123571662#u32, 303176864#u32,
      2137685056#u32, 1759609530#u32, 1418928155#u32, 71608334#u32
      ],
    Array.make 16#usize [
      6616262#u32, 1684515814#u32, 1721194338#u32, 720801691#u32,
      878392254#u32, 460379263#u32, 87930647#u32, 940673483#u32,
      1136203256#u32, 551499412#u32, 256220454#u32, 2007034235#u32,
      796124985#u32, 410436345#u32, 1705042586#u32, 1286336446#u32
      ],
    Array.make 16#usize [
      1522340456#u32, 1295296352#u32, 309794713#u32, 1772145068#u32,
      956898901#u32, 2137070800#u32, 988829146#u32, 2059451359#u32,
      1846491684#u32, 1105442551#u32, 1236497773#u32, 1452000568#u32,
      549485016#u32, 385992492#u32, 1987107948#u32, 1514377269#u32
      ],
    Array.make 16#usize [
      2090065934#u32, 1444920141#u32, 293113979#u32, 41120774#u32,
      855319793#u32, 1663284746#u32, 1789994008#u32, 1120509162#u32,
      358222743#u32, 1406256810#u32, 735183687#u32, 664485235#u32,
      1331641456#u32, 38121324#u32, 595810771#u32, 1234594393#u32
      ]
    ]

/-- [aspis_r1_mask_extraction_probe::poseidon2::EXTERNAL_INITIAL]
    Source: 'src/statement/poseidon2.rs', lines 83:0-104:2 -/
@[global_simps, irreducible]
def poseidon2.EXTERNAL_INITIAL : Array (Array Std.U32 16#usize) 4#usize :=
  Array.make 4#usize [
    Array.make 16#usize [
      1988864850#u32, 1893772157#u32, 1025928330#u32, 1839472709#u32,
      1611656994#u32, 1104858731#u32, 1694088660#u32, 1564660990#u32,
      1991332205#u32, 1875486487#u32, 1890340790#u32, 1658614#u32,
      582370530#u32, 528029397#u32, 1196956642#u32, 655401251#u32
      ],
    Array.make 16#usize [
      1652877415#u32, 26032894#u32, 1576640243#u32, 1277052539#u32,
      1450142396#u32, 697623591#u32, 1401580866#u32, 1568404175#u32,
      2145004971#u32, 265835716#u32, 1183985610#u32, 1031234465#u32,
      436012490#u32, 172735299#u32, 352802897#u32, 1032863094#u32
      ],
    Array.make 16#usize [
      757665783#u32, 1082171296#u32, 1507509996#u32, 309929890#u32,
      1807683232#u32, 43258895#u32, 611592566#u32, 1854193793#u32,
      575164234#u32, 894217817#u32, 72613857#u32, 1061659596#u32, 8921166#u32,
      1617355017#u32, 998001536#u32, 1800758877#u32
      ],
    Array.make 16#usize [
      1002748055#u32, 1935405944#u32, 1351462722#u32, 411368491#u32,
      1913975372#u32, 1956167178#u32, 442558016#u32, 855898408#u32,
      699687798#u32, 1553382248#u32, 1708169125#u32, 490049183#u32,
      1251643415#u32, 1193594742#u32, 880473871#u32, 511174042#u32
      ]
    ]


end FIq_Native
