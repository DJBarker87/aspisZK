import SelectedClaimProofs
/-! Minimal exact generated source cut for `composition_parts` closure gathers.
Source blocks are copied from sealed candidate Funs/Types pins listed in
`source-map.json`; declarations are relocated under a fresh namespace to avoid
stale-object collisions. -/
set_option autoImplicit false
open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe
/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::composition_parts::closure#1]
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 1247:58-1247:100 -/
@[reducible]
def AspisR1CompositionPartsGatherCut.pool_v1.pair_forest_semantic_terminal.composition_parts.closure_1 :=
  Array field.QM31 84#usize

/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::composition_parts::closure#2]
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 1248:63-1248:105 -/
@[reducible]
def AspisR1CompositionPartsGatherCut.pool_v1.pair_forest_semantic_terminal.composition_parts.closure_2 :=
  Array field.QM31 84#usize

/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::composition_parts::closure#3]
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 1249:64-1249:106 -/
@[reducible]
def AspisR1CompositionPartsGatherCut.pool_v1.pair_forest_semantic_terminal.composition_parts.closure_3 :=
  Array field.QM31 84#usize

/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::composition_parts::closure#4]
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 1251:67-1257:5 -/
@[reducible]
def AspisR1CompositionPartsGatherCut.pool_v1.pair_forest_semantic_terminal.composition_parts.closure_4 :=
  Array field.QM31 84#usize

/-- [aspis_r1_mask_extraction_probe::field::{impl core::clone::Clone for aspis_r1_mask_extraction_probe::field::QM31}::clone]:
    Source: 'src/field.rs', lines 431:9-431:14
    Visibility: public -/
def AspisR1CompositionPartsGatherCut.field.QM31.Insts.CoreCloneClone.clone
  (self : field.QM31) : Result field.QM31 := do
  ok self

/-- Trait implementation: [aspis_r1_mask_extraction_probe::field::{impl core::clone::Clone for aspis_r1_mask_extraction_probe::field::QM31}]
    Source: 'src/field.rs', lines 431:9-431:14 -/
@[reducible]
def AspisR1CompositionPartsGatherCut.field.QM31.Insts.CoreCloneClone : core.clone.Clone field.QM31 := {
  clone := AspisR1CompositionPartsGatherCut.field.QM31.Insts.CoreCloneClone.clone
}

/-- Trait implementation: [aspis_r1_mask_extraction_probe::field::{impl core::marker::Copy for aspis_r1_mask_extraction_probe::field::QM31}]
    Source: 'src/field.rs', lines 431:16-431:20 -/
@[reducible]
def AspisR1CompositionPartsGatherCut.field.QM31.Insts.CoreMarkerCopy : core.marker.Copy field.QM31 := {
  cloneInst := AspisR1CompositionPartsGatherCut.field.QM31.Insts.CoreCloneClone
}

/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::composition_parts::{impl core::ops::function::FnMut<(usize,), aspis_r1_mask_extraction_probe::field::QM31> for aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::composition_parts::closure#1<'_0>}::call_mut]:
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 1247:58-1247:100 -/
def
  AspisR1CompositionPartsGatherCut.pool_v1.pair_forest_semantic_terminal.composition_parts.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
  (c : AspisR1CompositionPartsGatherCut.pool_v1.pair_forest_semantic_terminal.composition_parts.closure_1)
  (tupled_args : Std.Usize) :
  Result (field.QM31 ×
    AspisR1CompositionPartsGatherCut.pool_v1.pair_forest_semantic_terminal.composition_parts.closure_1)
  := do
  let q ←
    AspisR1SelectedMaskProbe.pool_v1.pair_forest_semantic_terminal.selected_claim c 0#usize tupled_args
  ok (q, c)

/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::composition_parts::{impl core::ops::function::FnOnce<(usize,), aspis_r1_mask_extraction_probe::field::QM31> for aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::composition_parts::closure#1<'_0>}::call_once]:
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 1247:58-1247:100 -/
def
  AspisR1CompositionPartsGatherCut.pool_v1.pair_forest_semantic_terminal.composition_parts.closure_1.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31.call_once
  (c : AspisR1CompositionPartsGatherCut.pool_v1.pair_forest_semantic_terminal.composition_parts.closure_1)
  (i : Std.Usize) :
  Result field.QM31
  := do
  let (q, _) ←
    AspisR1CompositionPartsGatherCut.pool_v1.pair_forest_semantic_terminal.composition_parts.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
      c i
  ok q

/-- Trait implementation: [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::composition_parts::{impl core::ops::function::FnOnce<(usize,), aspis_r1_mask_extraction_probe::field::QM31> for aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::composition_parts::closure#1<'_0>}]
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 1247:58-1247:100 -/
@[reducible]
def
  AspisR1CompositionPartsGatherCut.pool_v1.pair_forest_semantic_terminal.composition_parts.closure_1.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31
  : core.ops.function.FnOnce
  AspisR1CompositionPartsGatherCut.pool_v1.pair_forest_semantic_terminal.composition_parts.closure_1 Std.Usize
  field.QM31 := {
  call_once :=
    AspisR1CompositionPartsGatherCut.pool_v1.pair_forest_semantic_terminal.composition_parts.closure_1.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31.call_once
}

/-- Trait implementation: [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::composition_parts::{impl core::ops::function::FnMut<(usize,), aspis_r1_mask_extraction_probe::field::QM31> for aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::composition_parts::closure#1<'_0>}]
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 1247:58-1247:100 -/
@[reducible]
def
  AspisR1CompositionPartsGatherCut.pool_v1.pair_forest_semantic_terminal.composition_parts.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeQM31
  : core.ops.function.FnMut
  AspisR1CompositionPartsGatherCut.pool_v1.pair_forest_semantic_terminal.composition_parts.closure_1 Std.Usize
  field.QM31 := {
  FnOnceInst :=
    AspisR1CompositionPartsGatherCut.pool_v1.pair_forest_semantic_terminal.composition_parts.closure_1.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31
  call_mut :=
    AspisR1CompositionPartsGatherCut.pool_v1.pair_forest_semantic_terminal.composition_parts.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
}

/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::composition_parts::{impl core::ops::function::FnMut<(usize,), aspis_r1_mask_extraction_probe::field::QM31> for aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::composition_parts::closure#2<'_0>}::call_mut]:
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 1248:63-1248:105 -/
def
  AspisR1CompositionPartsGatherCut.pool_v1.pair_forest_semantic_terminal.composition_parts.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
  (c : AspisR1CompositionPartsGatherCut.pool_v1.pair_forest_semantic_terminal.composition_parts.closure_2)
  (tupled_args : Std.Usize) :
  Result (field.QM31 ×
    AspisR1CompositionPartsGatherCut.pool_v1.pair_forest_semantic_terminal.composition_parts.closure_2)
  := do
  let q ←
    AspisR1SelectedMaskProbe.pool_v1.pair_forest_semantic_terminal.selected_claim c 1#usize tupled_args
  ok (q, c)

/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::composition_parts::{impl core::ops::function::FnOnce<(usize,), aspis_r1_mask_extraction_probe::field::QM31> for aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::composition_parts::closure#2<'_0>}::call_once]:
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 1248:63-1248:105 -/
def
  AspisR1CompositionPartsGatherCut.pool_v1.pair_forest_semantic_terminal.composition_parts.closure_2.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31.call_once
  (c : AspisR1CompositionPartsGatherCut.pool_v1.pair_forest_semantic_terminal.composition_parts.closure_2)
  (i : Std.Usize) :
  Result field.QM31
  := do
  let (q, _) ←
    AspisR1CompositionPartsGatherCut.pool_v1.pair_forest_semantic_terminal.composition_parts.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
      c i
  ok q

/-- Trait implementation: [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::composition_parts::{impl core::ops::function::FnOnce<(usize,), aspis_r1_mask_extraction_probe::field::QM31> for aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::composition_parts::closure#2<'_0>}]
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 1248:63-1248:105 -/
@[reducible]
def
  AspisR1CompositionPartsGatherCut.pool_v1.pair_forest_semantic_terminal.composition_parts.closure_2.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31
  : core.ops.function.FnOnce
  AspisR1CompositionPartsGatherCut.pool_v1.pair_forest_semantic_terminal.composition_parts.closure_2 Std.Usize
  field.QM31 := {
  call_once :=
    AspisR1CompositionPartsGatherCut.pool_v1.pair_forest_semantic_terminal.composition_parts.closure_2.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31.call_once
}

/-- Trait implementation: [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::composition_parts::{impl core::ops::function::FnMut<(usize,), aspis_r1_mask_extraction_probe::field::QM31> for aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::composition_parts::closure#2<'_0>}]
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 1248:63-1248:105 -/
@[reducible]
def
  AspisR1CompositionPartsGatherCut.pool_v1.pair_forest_semantic_terminal.composition_parts.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeQM31
  : core.ops.function.FnMut
  AspisR1CompositionPartsGatherCut.pool_v1.pair_forest_semantic_terminal.composition_parts.closure_2 Std.Usize
  field.QM31 := {
  FnOnceInst :=
    AspisR1CompositionPartsGatherCut.pool_v1.pair_forest_semantic_terminal.composition_parts.closure_2.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31
  call_mut :=
    AspisR1CompositionPartsGatherCut.pool_v1.pair_forest_semantic_terminal.composition_parts.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
}

/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::composition_parts::{impl core::ops::function::FnMut<(usize,), aspis_r1_mask_extraction_probe::field::QM31> for aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::composition_parts::closure#3<'_0>}::call_mut]:
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 1249:64-1249:106 -/
def
  AspisR1CompositionPartsGatherCut.pool_v1.pair_forest_semantic_terminal.composition_parts.closure_3.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
  (c : AspisR1CompositionPartsGatherCut.pool_v1.pair_forest_semantic_terminal.composition_parts.closure_3)
  (tupled_args : Std.Usize) :
  Result (field.QM31 ×
    AspisR1CompositionPartsGatherCut.pool_v1.pair_forest_semantic_terminal.composition_parts.closure_3)
  := do
  let q ←
    AspisR1SelectedMaskProbe.pool_v1.pair_forest_semantic_terminal.selected_claim c 2#usize tupled_args
  ok (q, c)

/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::composition_parts::{impl core::ops::function::FnOnce<(usize,), aspis_r1_mask_extraction_probe::field::QM31> for aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::composition_parts::closure#3<'_0>}::call_once]:
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 1249:64-1249:106 -/
def
  AspisR1CompositionPartsGatherCut.pool_v1.pair_forest_semantic_terminal.composition_parts.closure_3.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31.call_once
  (c : AspisR1CompositionPartsGatherCut.pool_v1.pair_forest_semantic_terminal.composition_parts.closure_3)
  (i : Std.Usize) :
  Result field.QM31
  := do
  let (q, _) ←
    AspisR1CompositionPartsGatherCut.pool_v1.pair_forest_semantic_terminal.composition_parts.closure_3.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
      c i
  ok q

/-- Trait implementation: [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::composition_parts::{impl core::ops::function::FnOnce<(usize,), aspis_r1_mask_extraction_probe::field::QM31> for aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::composition_parts::closure#3<'_0>}]
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 1249:64-1249:106 -/
@[reducible]
def
  AspisR1CompositionPartsGatherCut.pool_v1.pair_forest_semantic_terminal.composition_parts.closure_3.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31
  : core.ops.function.FnOnce
  AspisR1CompositionPartsGatherCut.pool_v1.pair_forest_semantic_terminal.composition_parts.closure_3 Std.Usize
  field.QM31 := {
  call_once :=
    AspisR1CompositionPartsGatherCut.pool_v1.pair_forest_semantic_terminal.composition_parts.closure_3.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31.call_once
}

/-- Trait implementation: [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::composition_parts::{impl core::ops::function::FnMut<(usize,), aspis_r1_mask_extraction_probe::field::QM31> for aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::composition_parts::closure#3<'_0>}]
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 1249:64-1249:106 -/
@[reducible]
def
  AspisR1CompositionPartsGatherCut.pool_v1.pair_forest_semantic_terminal.composition_parts.closure_3.Insts.CoreOpsFunctionFnMutTupleUsizeQM31
  : core.ops.function.FnMut
  AspisR1CompositionPartsGatherCut.pool_v1.pair_forest_semantic_terminal.composition_parts.closure_3 Std.Usize
  field.QM31 := {
  FnOnceInst :=
    AspisR1CompositionPartsGatherCut.pool_v1.pair_forest_semantic_terminal.composition_parts.closure_3.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31
  call_mut :=
    AspisR1CompositionPartsGatherCut.pool_v1.pair_forest_semantic_terminal.composition_parts.closure_3.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
}

/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::composition_parts::{impl core::ops::function::FnMut<(usize,), aspis_r1_mask_extraction_probe::field::QM31> for aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::composition_parts::closure#4<'_0>}::call_mut]:
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 1251:67-1257:5 -/
def
  AspisR1CompositionPartsGatherCut.pool_v1.pair_forest_semantic_terminal.composition_parts.closure_4.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
  (c : AspisR1CompositionPartsGatherCut.pool_v1.pair_forest_semantic_terminal.composition_parts.closure_4)
  (tupled_args : Std.Usize) :
  Result (field.QM31 ×
    AspisR1CompositionPartsGatherCut.pool_v1.pair_forest_semantic_terminal.composition_parts.closure_4)
  := do
  let i ←
    AspisR1SelectedMaskProbe.pool_v1.pair_forest_semantic_terminal.POOL_V1_PAIR_FOREST_TERMINAL_C1_COLUMNS_V1
      + tupled_args
  let q ← AspisR1SelectedMaskProbe.pool_v1.pair_forest_semantic_terminal.selected_claim c 0#usize i
  ok (q, c)

/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::composition_parts::{impl core::ops::function::FnOnce<(usize,), aspis_r1_mask_extraction_probe::field::QM31> for aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::composition_parts::closure#4<'_0>}::call_once]:
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 1251:67-1257:5 -/
def
  AspisR1CompositionPartsGatherCut.pool_v1.pair_forest_semantic_terminal.composition_parts.closure_4.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31.call_once
  (c : AspisR1CompositionPartsGatherCut.pool_v1.pair_forest_semantic_terminal.composition_parts.closure_4)
  (i : Std.Usize) :
  Result field.QM31
  := do
  let (q, _) ←
    AspisR1CompositionPartsGatherCut.pool_v1.pair_forest_semantic_terminal.composition_parts.closure_4.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
      c i
  ok q

/-- Trait implementation: [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::composition_parts::{impl core::ops::function::FnOnce<(usize,), aspis_r1_mask_extraction_probe::field::QM31> for aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::composition_parts::closure#4<'_0>}]
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 1251:67-1257:5 -/
@[reducible]
def
  AspisR1CompositionPartsGatherCut.pool_v1.pair_forest_semantic_terminal.composition_parts.closure_4.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31
  : core.ops.function.FnOnce
  AspisR1CompositionPartsGatherCut.pool_v1.pair_forest_semantic_terminal.composition_parts.closure_4 Std.Usize
  field.QM31 := {
  call_once :=
    AspisR1CompositionPartsGatherCut.pool_v1.pair_forest_semantic_terminal.composition_parts.closure_4.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31.call_once
}

/-- Trait implementation: [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::composition_parts::{impl core::ops::function::FnMut<(usize,), aspis_r1_mask_extraction_probe::field::QM31> for aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::composition_parts::closure#4<'_0>}]
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 1251:67-1257:5 -/
@[reducible]
def
  AspisR1CompositionPartsGatherCut.pool_v1.pair_forest_semantic_terminal.composition_parts.closure_4.Insts.CoreOpsFunctionFnMutTupleUsizeQM31
  : core.ops.function.FnMut
  AspisR1CompositionPartsGatherCut.pool_v1.pair_forest_semantic_terminal.composition_parts.closure_4 Std.Usize
  field.QM31 := {
  FnOnceInst :=
    AspisR1CompositionPartsGatherCut.pool_v1.pair_forest_semantic_terminal.composition_parts.closure_4.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31
  call_mut :=
    AspisR1CompositionPartsGatherCut.pool_v1.pair_forest_semantic_terminal.composition_parts.closure_4.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
}
