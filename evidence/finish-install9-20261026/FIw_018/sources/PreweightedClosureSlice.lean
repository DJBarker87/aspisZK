import SelectorSourceSlice
import ArrayFromFnCopyStable
open Aeneas Aeneas.Std Result
set_option autoImplicit false
namespace AspisR1PreweightedCandidate
open AspisR1SelectedMaskProbe

/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::add_preweighted::closure]
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 114:77-121:9 -/
def pool_v1.pair_forest_semantic_terminal.add_preweighted.closure (N :
  Std.Usize) :=
  Std.Usize × Std.Usize × Array field.QM31 N

/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::add_preweighted::{impl core::ops::function::FnMut<(usize,), aspis_r1_mask_extraction_probe::field::QM31> for aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::add_preweighted::closure<'_0, '_1, '_2, N>}::call_mut]:
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 114:77-121:9 -/
def
  pool_v1.pair_forest_semantic_terminal.add_preweighted.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
  {N : Std.Usize}
  (c : pool_v1.pair_forest_semantic_terminal.add_preweighted.closure N)
  (tupled_args : Std.Usize) :
  Result (field.QM31 ×
    (pool_v1.pair_forest_semantic_terminal.add_preweighted.closure N))
  := do
  let (i, i1, a) := c
  let i2 ← 4#usize * i
  let source ← i2 + tupled_args
  if source >= i1
  then
    let i3 ← i1 + N
    if source < i3
    then let i4 ← source - i1
         let q ← Array.index_usize a i4
         ok (q, c)
    else ok (field.QM31.ZERO, c)
  else ok (field.QM31.ZERO, c)

/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::add_preweighted::{impl core::ops::function::FnOnce<(usize,), aspis_r1_mask_extraction_probe::field::QM31> for aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::add_preweighted::closure<'_0, '_1, '_2, N>}::call_once]:
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 114:77-121:9 -/
def
  pool_v1.pair_forest_semantic_terminal.add_preweighted.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31.call_once
  {N : Std.Usize}
  (c : pool_v1.pair_forest_semantic_terminal.add_preweighted.closure N)
  (i : Std.Usize) :
  Result field.QM31
  := do
  let (q, _) ←
    pool_v1.pair_forest_semantic_terminal.add_preweighted.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
      c i
  ok q

/-- Trait implementation: [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::add_preweighted::{impl core::ops::function::FnOnce<(usize,), aspis_r1_mask_extraction_probe::field::QM31> for aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::add_preweighted::closure<'_0, '_1, '_2, N>}]
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 114:77-121:9 -/
@[reducible]
def
  pool_v1.pair_forest_semantic_terminal.add_preweighted.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31
  (N : Std.Usize) : core.ops.function.FnOnce
  (pool_v1.pair_forest_semantic_terminal.add_preweighted.closure N) Std.Usize
  field.QM31 := {
  call_once :=
    pool_v1.pair_forest_semantic_terminal.add_preweighted.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31.call_once
}

/-- Trait implementation: [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::add_preweighted::{impl core::ops::function::FnMut<(usize,), aspis_r1_mask_extraction_probe::field::QM31> for aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::add_preweighted::closure<'_0, '_1, '_2, N>}]
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 114:77-121:9 -/
@[reducible]
def
  pool_v1.pair_forest_semantic_terminal.add_preweighted.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31
  (N : Std.Usize) : core.ops.function.FnMut
  (pool_v1.pair_forest_semantic_terminal.add_preweighted.closure N) Std.Usize
  field.QM31 := {
  FnOnceInst :=
    pool_v1.pair_forest_semantic_terminal.add_preweighted.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31
    N
  call_mut :=
    pool_v1.pair_forest_semantic_terminal.add_preweighted.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
}


end AspisR1PreweightedCandidate
