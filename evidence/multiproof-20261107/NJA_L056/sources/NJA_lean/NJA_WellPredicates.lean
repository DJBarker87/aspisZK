import NJA_Small
open Aeneas Aeneas.Std Result ControlFlow Error
noncomputable section
namespace NJA_Multiproof
def
  multiproof.well_formed.closure_1.Insts.CoreOpsFunctionFnMutTupleSharedU32Bool.call_mut
  (c : multiproof.well_formed.closure_1) (tupled_args : Std.U32) :
  Result (Bool × multiproof.well_formed.closure_1)
  := do
  let i ← lift (Std.U32.wrapping_shl 1#u32 multiproof.LEAF_BITS)
  ok (tupled_args < i, c)

/-- [aspis_r1_cost_probe::multiproof::well_formed::{impl core::ops::function::FnOnce<(&'_ u32,), bool> for aspis_r1_cost_probe::multiproof::well_formed::closure#1}::call_once]:
    Source: 'crates/aspis-r1-cost-probe/src/multiproof.rs', lines 58:30-58:53 -/
def
  multiproof.well_formed.closure_1.Insts.CoreOpsFunctionFnOnceTupleSharedU32Bool.call_once
  (c : multiproof.well_formed.closure_1) (i : Std.U32) : Result Bool := do
  let (b, _) ←
    multiproof.well_formed.closure_1.Insts.CoreOpsFunctionFnMutTupleSharedU32Bool.call_mut
      c i
  ok b

/-- Trait implementation: [aspis_r1_cost_probe::multiproof::well_formed::{impl core::ops::function::FnOnce<(&'_ u32,), bool> for aspis_r1_cost_probe::multiproof::well_formed::closure#1}]
    Source: 'crates/aspis-r1-cost-probe/src/multiproof.rs', lines 58:30-58:53 -/
@[reducible]
def
  multiproof.well_formed.closure_1.Insts.CoreOpsFunctionFnOnceTupleSharedU32Bool
  : core.ops.function.FnOnce multiproof.well_formed.closure_1 Std.U32 Bool := {
  call_once :=
    multiproof.well_formed.closure_1.Insts.CoreOpsFunctionFnOnceTupleSharedU32Bool.call_once
}

/-- Trait implementation: [aspis_r1_cost_probe::multiproof::well_formed::{impl core::ops::function::FnMut<(&'_ u32,), bool> for aspis_r1_cost_probe::multiproof::well_formed::closure#1}]
    Source: 'crates/aspis-r1-cost-probe/src/multiproof.rs', lines 58:30-58:53 -/
@[reducible]
def
  multiproof.well_formed.closure_1.Insts.CoreOpsFunctionFnMutTupleSharedU32Bool
  : core.ops.function.FnMut multiproof.well_formed.closure_1 Std.U32 Bool := {
  FnOnceInst :=
    multiproof.well_formed.closure_1.Insts.CoreOpsFunctionFnOnceTupleSharedU32Bool
  call_mut :=
    multiproof.well_formed.closure_1.Insts.CoreOpsFunctionFnMutTupleSharedU32Bool.call_mut
}

/-- [aspis_r1_cost_probe::multiproof::well_formed::{impl core::ops::function::FnMut<(&'_ [u32],), bool> for aspis_r1_cost_probe::multiproof::well_formed::closure}::call_mut]:
    Source: 'crates/aspis-r1-cost-probe/src/multiproof.rs', lines 57:34-57:49 -/
def
  multiproof.well_formed.closure.Insts.CoreOpsFunctionFnMutTupleSharedSliceU32Bool.call_mut
  (c : multiproof.well_formed.closure) (tupled_args : Slice Std.U32) :
  Result (Bool × multiproof.well_formed.closure)
  := do
  let i ← Slice.index_usize tupled_args 0#usize
  let i1 ← Slice.index_usize tupled_args 1#usize
  ok (i < i1, c)

/-- [aspis_r1_cost_probe::multiproof::well_formed::{impl core::ops::function::FnOnce<(&'_ [u32],), bool> for aspis_r1_cost_probe::multiproof::well_formed::closure}::call_once]:
    Source: 'crates/aspis-r1-cost-probe/src/multiproof.rs', lines 57:34-57:49 -/
def
  multiproof.well_formed.closure.Insts.CoreOpsFunctionFnOnceTupleSharedSliceU32Bool.call_once
  (c : multiproof.well_formed.closure) (s : Slice Std.U32) : Result Bool := do
  let (b, _) ←
    multiproof.well_formed.closure.Insts.CoreOpsFunctionFnMutTupleSharedSliceU32Bool.call_mut
      c s
  ok b

/-- Trait implementation: [aspis_r1_cost_probe::multiproof::well_formed::{impl core::ops::function::FnOnce<(&'_ [u32],), bool> for aspis_r1_cost_probe::multiproof::well_formed::closure}]
    Source: 'crates/aspis-r1-cost-probe/src/multiproof.rs', lines 57:34-57:49 -/
@[reducible]
def
  multiproof.well_formed.closure.Insts.CoreOpsFunctionFnOnceTupleSharedSliceU32Bool
  : core.ops.function.FnOnce multiproof.well_formed.closure (Slice Std.U32)
  Bool := {
  call_once :=
    multiproof.well_formed.closure.Insts.CoreOpsFunctionFnOnceTupleSharedSliceU32Bool.call_once
}

/-- Trait implementation: [aspis_r1_cost_probe::multiproof::well_formed::{impl core::ops::function::FnMut<(&'_ [u32],), bool> for aspis_r1_cost_probe::multiproof::well_formed::closure}]
    Source: 'crates/aspis-r1-cost-probe/src/multiproof.rs', lines 57:34-57:49 -/
@[reducible]
def
  multiproof.well_formed.closure.Insts.CoreOpsFunctionFnMutTupleSharedSliceU32Bool
  : core.ops.function.FnMut multiproof.well_formed.closure (Slice Std.U32) Bool
  := {
  FnOnceInst :=
    multiproof.well_formed.closure.Insts.CoreOpsFunctionFnOnceTupleSharedSliceU32Bool
  call_mut :=
    multiproof.well_formed.closure.Insts.CoreOpsFunctionFnMutTupleSharedSliceU32Bool.call_mut
}


end NJA_Multiproof
