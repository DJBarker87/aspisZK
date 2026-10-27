-- Minimal generated G callback slice; selected generated declarations below are byte-identical to G.
import Aeneas.Std
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048

namespace AspisR1SelectedMaskProbe

/-- [aspis_r1_mask_extraction_probe::state_only_poseidon::external_linear_lazy_row::closure]
    Source: 'src/statement/state_only_poseidon.rs', lines 144:43-156:13 -/
def state_only_poseidon.external_linear_lazy_row.closure :=
  Array (Array Std.U32 4#usize) 4#usize × Std.Usize

/-- [aspis_r1_mask_extraction_probe::state_only_poseidon::external_linear_lazy_row::{impl core::ops::function::FnMut<(usize,), u64> for aspis_r1_mask_extraction_probe::state_only_poseidon::external_linear_lazy_row::closure<'_0, '_1>}::call_mut]:
    Source: 'src/statement/state_only_poseidon.rs', lines 144:43-156:13 -/
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
    Source: 'src/statement/state_only_poseidon.rs', lines 144:43-156:13 -/
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
    Source: 'src/statement/state_only_poseidon.rs', lines 144:43-156:13 -/
@[reducible]
def
  state_only_poseidon.external_linear_lazy_row.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeU64
  : core.ops.function.FnOnce
  state_only_poseidon.external_linear_lazy_row.closure Std.Usize Std.U64 := {
  call_once :=
    state_only_poseidon.external_linear_lazy_row.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeU64.call_once
}

/-- Trait implementation: [aspis_r1_mask_extraction_probe::state_only_poseidon::external_linear_lazy_row::{impl core::ops::function::FnMut<(usize,), u64> for aspis_r1_mask_extraction_probe::state_only_poseidon::external_linear_lazy_row::closure<'_0, '_1>}]
    Source: 'src/statement/state_only_poseidon.rs', lines 144:43-156:13 -/
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

end AspisR1SelectedMaskProbe
