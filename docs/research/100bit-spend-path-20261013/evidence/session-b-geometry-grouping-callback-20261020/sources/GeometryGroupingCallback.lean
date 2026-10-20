import AspisR1GeometryGrouping.Types
open Aeneas Aeneas.Std Result ControlFlow Error
set_option autoImplicit false
noncomputable section
namespace AspisR1GeometryGrouping

/-- [aspis_r1_stage2_adopted_caller::geometry_groups::closure::{impl core::ops::function::FnMut<(usize,), aspis_r1_stage2_adopted_caller::M31> for aspis_r1_stage2_adopted_caller::geometry_groups::closure::closure<'_0, '_1>}::call_mut]:
    Source: 'lib.rs', lines 5:53-5:75 -/
def
  geometry_groups.closure.closure.Insts.CoreOpsFunctionFnMutTupleUsizeM31.call_mut
  (c : geometry_groups.closure.closure) (tupled_args : Std.Usize) :
  Result (M31 × geometry_groups.closure.closure)
  := do
  let (v, i) := c
  let i1 ← 5#usize * i
  let i2 ← i1 + tupled_args
  let m ←
    alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice M31) v i2
  ok (m, c)

/-- [aspis_r1_stage2_adopted_caller::geometry_groups::closure::{impl core::ops::function::FnOnce<(usize,), aspis_r1_stage2_adopted_caller::M31> for aspis_r1_stage2_adopted_caller::geometry_groups::closure::closure<'_0, '_1>}::call_once]:
    Source: 'lib.rs', lines 5:53-5:75 -/
def
  geometry_groups.closure.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeM31.call_once
  (c : geometry_groups.closure.closure) (i : Std.Usize) : Result M31 := do
  let (m, _) ←
    geometry_groups.closure.closure.Insts.CoreOpsFunctionFnMutTupleUsizeM31.call_mut
      c i
  ok m

/-- Trait implementation: [aspis_r1_stage2_adopted_caller::geometry_groups::closure::{impl core::ops::function::FnOnce<(usize,), aspis_r1_stage2_adopted_caller::M31> for aspis_r1_stage2_adopted_caller::geometry_groups::closure::closure<'_0, '_1>}]
    Source: 'lib.rs', lines 5:53-5:75 -/
@[reducible]
def geometry_groups.closure.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeM31 :
  core.ops.function.FnOnce geometry_groups.closure.closure Std.Usize M31 := {
  call_once :=
    geometry_groups.closure.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeM31.call_once
}

/-- Trait implementation: [aspis_r1_stage2_adopted_caller::geometry_groups::closure::{impl core::ops::function::FnMut<(usize,), aspis_r1_stage2_adopted_caller::M31> for aspis_r1_stage2_adopted_caller::geometry_groups::closure::closure<'_0, '_1>}]
    Source: 'lib.rs', lines 5:53-5:75 -/
@[reducible]
def geometry_groups.closure.closure.Insts.CoreOpsFunctionFnMutTupleUsizeM31 :
  core.ops.function.FnMut geometry_groups.closure.closure Std.Usize M31 := {
  FnOnceInst :=
    geometry_groups.closure.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeM31
  call_mut :=
    geometry_groups.closure.closure.Insts.CoreOpsFunctionFnMutTupleUsizeM31.call_mut
}

end AspisR1GeometryGrouping
