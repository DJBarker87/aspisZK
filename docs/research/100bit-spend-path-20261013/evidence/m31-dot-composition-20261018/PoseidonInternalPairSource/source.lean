import PoseidonM31DotSource

/-! Exact missing internal-pair carriers, callbacks, row table and wrapper
from candidate Funs f1e258056294e84777f56f2a1ea3572329eca52b4bb553bfc6c58027bef1604c
and Types f41e6844fe7c10fbabc0b2a37d2b63d820b62d5a83cf1c75b91ac7b428853a38.
Existing internal round, internal constants and scalar-weight dot owners are
imported unchanged. -/
namespace AspisR1SelectedMaskProbe
open Aeneas Aeneas.Std Result
/-- [aspis_r1_mask_extraction_probe::state_only_poseidon::interpolated_internal_pair::closure#2]
    Source: 'src/statement/state_only_poseidon.rs', lines 535:33-535:71 -/
@[reducible]
def state_only_poseidon.interpolated_internal_pair.closure_2 := Unit

/-- [aspis_r1_mask_extraction_probe::state_only_poseidon::interpolated_internal_pair::closure#1]
    Source: 'src/statement/state_only_poseidon.rs', lines 534:34-534:68 -/
@[reducible]
def state_only_poseidon.interpolated_internal_pair.closure_1 := Unit

/-- [aspis_r1_mask_extraction_probe::state_only_poseidon::interpolated_internal_pair::closure]
    Source: 'src/statement/state_only_poseidon.rs', lines 533:27-533:43 -/
@[reducible]
def state_only_poseidon.interpolated_internal_pair.closure :=
  Array field.QM31 16#usize

/-- [aspis_r1_mask_extraction_probe::state_only_poseidon::interpolated_internal_pair::{impl core::ops::function::FnMut<(usize,), aspis_r1_mask_extraction_probe::field::M31> for aspis_r1_mask_extraction_probe::state_only_poseidon::interpolated_internal_pair::closure#2}::call_mut]:
    Source: 'src/statement/state_only_poseidon.rs', lines 535:33-535:71 -/
def
  state_only_poseidon.interpolated_internal_pair.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeM31.call_mut
  (c : state_only_poseidon.interpolated_internal_pair.closure_2)
  (tupled_args : Std.Usize) :
  Result (field.M31 ×
    state_only_poseidon.interpolated_internal_pair.closure_2)
  := do
  let i ← tupled_args - 2#usize
  let i1 ← 2#usize * i
  let i2 ← i1 + 1#usize
  let i3 ← Array.index_usize poseidon2.INTERNAL i2
  ok (i3, c)

/-- [aspis_r1_mask_extraction_probe::state_only_poseidon::interpolated_internal_pair::{impl core::ops::function::FnOnce<(usize,), aspis_r1_mask_extraction_probe::field::M31> for aspis_r1_mask_extraction_probe::state_only_poseidon::interpolated_internal_pair::closure#2}::call_once]:
    Source: 'src/statement/state_only_poseidon.rs', lines 535:33-535:71 -/
def
  state_only_poseidon.interpolated_internal_pair.closure_2.Insts.CoreOpsFunctionFnOnceTupleUsizeM31.call_once
  (c : state_only_poseidon.interpolated_internal_pair.closure_2)
  (i : Std.Usize) :
  Result field.M31
  := do
  let (m, _) ←
    state_only_poseidon.interpolated_internal_pair.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeM31.call_mut
      c i
  ok m

/-- Trait implementation: [aspis_r1_mask_extraction_probe::state_only_poseidon::interpolated_internal_pair::{impl core::ops::function::FnOnce<(usize,), aspis_r1_mask_extraction_probe::field::M31> for aspis_r1_mask_extraction_probe::state_only_poseidon::interpolated_internal_pair::closure#2}]
    Source: 'src/statement/state_only_poseidon.rs', lines 535:33-535:71 -/
@[reducible]
def
  state_only_poseidon.interpolated_internal_pair.closure_2.Insts.CoreOpsFunctionFnOnceTupleUsizeM31
  : core.ops.function.FnOnce
  state_only_poseidon.interpolated_internal_pair.closure_2 Std.Usize field.M31
  := {
  call_once :=
    state_only_poseidon.interpolated_internal_pair.closure_2.Insts.CoreOpsFunctionFnOnceTupleUsizeM31.call_once
}

/-- Trait implementation: [aspis_r1_mask_extraction_probe::state_only_poseidon::interpolated_internal_pair::{impl core::ops::function::FnMut<(usize,), aspis_r1_mask_extraction_probe::field::M31> for aspis_r1_mask_extraction_probe::state_only_poseidon::interpolated_internal_pair::closure#2}]
    Source: 'src/statement/state_only_poseidon.rs', lines 535:33-535:71 -/
@[reducible]
def
  state_only_poseidon.interpolated_internal_pair.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeM31
  : core.ops.function.FnMut
  state_only_poseidon.interpolated_internal_pair.closure_2 Std.Usize field.M31
  := {
  FnOnceInst :=
    state_only_poseidon.interpolated_internal_pair.closure_2.Insts.CoreOpsFunctionFnOnceTupleUsizeM31
  call_mut :=
    state_only_poseidon.interpolated_internal_pair.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeM31.call_mut
}

/-- [aspis_r1_mask_extraction_probe::state_only_poseidon::interpolated_internal_pair::{impl core::ops::function::FnMut<(usize,), aspis_r1_mask_extraction_probe::field::M31> for aspis_r1_mask_extraction_probe::state_only_poseidon::interpolated_internal_pair::closure#1}::call_mut]:
    Source: 'src/statement/state_only_poseidon.rs', lines 534:34-534:68 -/
def
  state_only_poseidon.interpolated_internal_pair.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeM31.call_mut
  (c : state_only_poseidon.interpolated_internal_pair.closure_1)
  (tupled_args : Std.Usize) :
  Result (field.M31 ×
    state_only_poseidon.interpolated_internal_pair.closure_1)
  := do
  let i ← tupled_args - 2#usize
  let i1 ← 2#usize * i
  let i2 ← Array.index_usize poseidon2.INTERNAL i1
  ok (i2, c)

/-- [aspis_r1_mask_extraction_probe::state_only_poseidon::interpolated_internal_pair::{impl core::ops::function::FnOnce<(usize,), aspis_r1_mask_extraction_probe::field::M31> for aspis_r1_mask_extraction_probe::state_only_poseidon::interpolated_internal_pair::closure#1}::call_once]:
    Source: 'src/statement/state_only_poseidon.rs', lines 534:34-534:68 -/
def
  state_only_poseidon.interpolated_internal_pair.closure_1.Insts.CoreOpsFunctionFnOnceTupleUsizeM31.call_once
  (c : state_only_poseidon.interpolated_internal_pair.closure_1)
  (i : Std.Usize) :
  Result field.M31
  := do
  let (m, _) ←
    state_only_poseidon.interpolated_internal_pair.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeM31.call_mut
      c i
  ok m

/-- Trait implementation: [aspis_r1_mask_extraction_probe::state_only_poseidon::interpolated_internal_pair::{impl core::ops::function::FnOnce<(usize,), aspis_r1_mask_extraction_probe::field::M31> for aspis_r1_mask_extraction_probe::state_only_poseidon::interpolated_internal_pair::closure#1}]
    Source: 'src/statement/state_only_poseidon.rs', lines 534:34-534:68 -/
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
    Source: 'src/statement/state_only_poseidon.rs', lines 534:34-534:68 -/
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
    Source: 'src/statement/state_only_poseidon.rs', lines 533:27-533:43 -/
def
  state_only_poseidon.interpolated_internal_pair.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
  (c : state_only_poseidon.interpolated_internal_pair.closure)
  (tupled_args : Std.Usize) :
  Result (field.QM31 × state_only_poseidon.interpolated_internal_pair.closure)
  := do
  let q ← Array.index_usize c tupled_args
  ok (q, c)

/-- [aspis_r1_mask_extraction_probe::state_only_poseidon::interpolated_internal_pair::{impl core::ops::function::FnOnce<(usize,), aspis_r1_mask_extraction_probe::field::QM31> for aspis_r1_mask_extraction_probe::state_only_poseidon::interpolated_internal_pair::closure<'_0>}::call_once]:
    Source: 'src/statement/state_only_poseidon.rs', lines 533:27-533:43 -/
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
    Source: 'src/statement/state_only_poseidon.rs', lines 533:27-533:43 -/
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
    Source: 'src/statement/state_only_poseidon.rs', lines 533:27-533:43 -/
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
    Source: 'src/statement/state_only_poseidon.rs', lines 532:4-532:51 -/
@[global_simps, irreducible]
def state_only_poseidon.interpolated_internal_pair.ROWS
  : Array Std.Usize 7#usize :=
  Array.make 7#usize [
    2#usize, 3#usize, 4#usize, 5#usize, 6#usize, 7#usize, 8#usize
    ]

/-- [aspis_r1_mask_extraction_probe::state_only_poseidon::interpolated_internal_pair]:
    Source: 'src/statement/state_only_poseidon.rs', lines 528:0-539:1 -/
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


end AspisR1SelectedMaskProbe
