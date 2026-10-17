import Aeneas
import EmptyRootExecution
import AspisR1SelectedMaskProbe.Funs
import RawPoseidonExternalRowWrapper
import SelectorValueLaneLoops012Slice

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
open Aeneas Aeneas.Std Result ControlFlow Error
namespace AspisR1SelectedMaskProbe

/-- [aspis_r1_mask_extraction_probe::poseidon2::POSEIDON2_WIDTH]
    Source: 'src/statement/poseidon2.rs', lines 56:0-56:38
    Visibility: public -/
@[global_simps, irreducible]
def poseidon2.POSEIDON2_WIDTH : Std.Usize := 16#usize


/-- [aspis_r1_mask_extraction_probe::state_only_poseidon::external_linear_lazy::closure#1]
    Source: 'src/statement/state_only_poseidon.rs', lines 190:88-192:9 -/
def state_only_poseidon.external_linear_lazy.closure_1 :=
  Array Std.U32 4#usize × Array (Array Std.U64 4#usize) 4#usize × Std.Usize

/-- [aspis_r1_mask_extraction_probe::state_only_poseidon::external_linear_lazy::closure::closure]
    Source: 'src/statement/state_only_poseidon.rs', lines 180:48-185:9 -/
def state_only_poseidon.external_linear_lazy.closure.closure :=
  Array field.QM31 16#usize × Std.Usize

/-- [aspis_r1_mask_extraction_probe::state_only_poseidon::external_linear_lazy::closure]
    Source: 'src/statement/state_only_poseidon.rs', lines 179:75-186:5 -/
@[reducible]
def state_only_poseidon.external_linear_lazy.closure :=
  Array field.QM31 16#usize

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

end AspisR1SelectedMaskProbe
