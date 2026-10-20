import Aeneas
import AspisR1SelectedMaskProbe.Types
import AspisR1SelectedMaskProbe.FunsExternal
import TerminalV4CompositionLoopsChunk06V5
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
noncomputable section
namespace AspisR1SelectedMaskProbe
def array_from_fn_copy_loop
  {T : Type} {T2 : Type} {N : Std.Usize} (coreopsfunctionFnMutT2TupleUsizeTInst
  : core.ops.function.FnMut T2 Std.Usize T) (f : T2) (out : Array T N)
  (i : Std.Usize) :
  Result (Array T N)
  := do
  if i < N
  then
    let (t, f1) ← coreopsfunctionFnMutT2TupleUsizeTInst.call_mut f i
    let a ← Array.update out i t
    let i1 ← i + 1#usize
    array_from_fn_copy_loop coreopsfunctionFnMutT2TupleUsizeTInst f1 a i1
  else ok out
partial_fixpoint

/-- [aspis_r1_mask_extraction_probe::array_from_fn_copy]:
    Source: 'src/lib.rs', lines 21:0-32:1 -/
def array_from_fn_copy
  {T : Type} {T2 : Type} (N : Std.Usize) (coremarkerCopyInst : core.marker.Copy
  T) (coreopsfunctionFnMutT2TupleUsizeTInst : core.ops.function.FnMut T2
  Std.Usize T) (init : T) (f : T2) :
  Result (Array T N)
  := do
  let out := Array.repeat N init
  array_from_fn_copy_loop coreopsfunctionFnMutT2TupleUsizeTInst f out 0#usize
/-- [aspis_r1_mask_extraction_probe::state_only_hiding::STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS]
    Source: 'src/state_only_hiding.rs', lines 13:0-13:61
    Visibility: public -/
@[global_simps, irreducible]
def state_only_hiding.STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS : Std.Usize :=
  10#usize
/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::POOL_V1_PAIR_FOREST_TERMINAL_C1_COLUMNS_V1]
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 29:0-29:65
    Visibility: public -/
@[global_simps, irreducible]
def
  pool_v1.pair_forest_semantic_terminal.POOL_V1_PAIR_FOREST_TERMINAL_C1_COLUMNS_V1
  : Std.Usize :=
  16#usize

/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::POOL_V1_PAIR_FOREST_SELECTED_TERMINAL_COLUMNS_V1]
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 31:0-32:92
    Visibility: public -/
@[global_simps, irreducible]
def
  pool_v1.pair_forest_semantic_terminal.POOL_V1_PAIR_FOREST_SELECTED_TERMINAL_COLUMNS_V1
  : Result Std.Usize := do
  let i ←
    pool_v1.pair_forest_semantic_terminal.POOL_V1_PAIR_FOREST_TERMINAL_C1_COLUMNS_V1
      + state_only_hiding.STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS
  i + 2#usize

/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::selected_claim]:
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 1199:0-1205:1 -/
def pool_v1.pair_forest_semantic_terminal.selected_claim
  (claims : Array field.QM31 84#usize) (point : Std.Usize) (column : Std.Usize)
  :
  Result field.QM31
  := do
  let i ←
    pool_v1.pair_forest_semantic_terminal.POOL_V1_PAIR_FOREST_SELECTED_TERMINAL_COLUMNS_V1
  let i1 ← point * i
  let i2 ← i1 + column
  Array.index_usize claims i2
/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::composition_parts::{impl core::ops::function::FnMut<(usize,), aspis_r1_mask_extraction_probe::field::QM31> for aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::composition_parts::closure#3<'_0>}::call_mut]:
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 1261:67-1267:5 -/
def
  pool_v1.pair_forest_semantic_terminal.composition_parts.closure_3.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
  (c : pool_v1.pair_forest_semantic_terminal.composition_parts.closure_3)
  (tupled_args : Std.Usize) :
  Result (field.QM31 ×
    pool_v1.pair_forest_semantic_terminal.composition_parts.closure_3)
  := do
  let i ←
    pool_v1.pair_forest_semantic_terminal.POOL_V1_PAIR_FOREST_TERMINAL_C1_COLUMNS_V1
      + tupled_args
  let q ← pool_v1.pair_forest_semantic_terminal.selected_claim c 0#usize i
  ok (q, c)

/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::composition_parts::{impl core::ops::function::FnOnce<(usize,), aspis_r1_mask_extraction_probe::field::QM31> for aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::composition_parts::closure#3<'_0>}::call_once]:
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 1261:67-1267:5 -/
def
  pool_v1.pair_forest_semantic_terminal.composition_parts.closure_3.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31.call_once
  (c : pool_v1.pair_forest_semantic_terminal.composition_parts.closure_3)
  (i : Std.Usize) :
  Result field.QM31
  := do
  let (q, _) ←
    pool_v1.pair_forest_semantic_terminal.composition_parts.closure_3.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
      c i
  ok q

/-- Trait implementation: [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::composition_parts::{impl core::ops::function::FnOnce<(usize,), aspis_r1_mask_extraction_probe::field::QM31> for aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::composition_parts::closure#3<'_0>}]
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 1261:67-1267:5 -/
@[reducible]
def
  pool_v1.pair_forest_semantic_terminal.composition_parts.closure_3.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31
  : core.ops.function.FnOnce
  pool_v1.pair_forest_semantic_terminal.composition_parts.closure_3 Std.Usize
  field.QM31 := {
  call_once :=
    pool_v1.pair_forest_semantic_terminal.composition_parts.closure_3.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31.call_once
}

/-- Trait implementation: [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::composition_parts::{impl core::ops::function::FnMut<(usize,), aspis_r1_mask_extraction_probe::field::QM31> for aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::composition_parts::closure#3<'_0>}]
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 1261:67-1267:5 -/
@[reducible]
def
  pool_v1.pair_forest_semantic_terminal.composition_parts.closure_3.Insts.CoreOpsFunctionFnMutTupleUsizeQM31
  : core.ops.function.FnMut
  pool_v1.pair_forest_semantic_terminal.composition_parts.closure_3 Std.Usize
  field.QM31 := {
  FnOnceInst :=
    pool_v1.pair_forest_semantic_terminal.composition_parts.closure_3.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31
  call_mut :=
    pool_v1.pair_forest_semantic_terminal.composition_parts.closure_3.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
}

/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::composition_parts::{impl core::ops::function::FnMut<(usize,), aspis_r1_mask_extraction_probe::field::QM31> for aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::composition_parts::closure#2<'_0>}::call_mut]:
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 1259:64-1259:106 -/
def
  pool_v1.pair_forest_semantic_terminal.composition_parts.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
  (c : pool_v1.pair_forest_semantic_terminal.composition_parts.closure_2)
  (tupled_args : Std.Usize) :
  Result (field.QM31 ×
    pool_v1.pair_forest_semantic_terminal.composition_parts.closure_2)
  := do
  let q ←
    pool_v1.pair_forest_semantic_terminal.selected_claim c 2#usize tupled_args
  ok (q, c)

/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::composition_parts::{impl core::ops::function::FnOnce<(usize,), aspis_r1_mask_extraction_probe::field::QM31> for aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::composition_parts::closure#2<'_0>}::call_once]:
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 1259:64-1259:106 -/
def
  pool_v1.pair_forest_semantic_terminal.composition_parts.closure_2.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31.call_once
  (c : pool_v1.pair_forest_semantic_terminal.composition_parts.closure_2)
  (i : Std.Usize) :
  Result field.QM31
  := do
  let (q, _) ←
    pool_v1.pair_forest_semantic_terminal.composition_parts.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
      c i
  ok q

/-- Trait implementation: [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::composition_parts::{impl core::ops::function::FnOnce<(usize,), aspis_r1_mask_extraction_probe::field::QM31> for aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::composition_parts::closure#2<'_0>}]
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 1259:64-1259:106 -/
@[reducible]
def
  pool_v1.pair_forest_semantic_terminal.composition_parts.closure_2.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31
  : core.ops.function.FnOnce
  pool_v1.pair_forest_semantic_terminal.composition_parts.closure_2 Std.Usize
  field.QM31 := {
  call_once :=
    pool_v1.pair_forest_semantic_terminal.composition_parts.closure_2.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31.call_once
}

/-- Trait implementation: [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::composition_parts::{impl core::ops::function::FnMut<(usize,), aspis_r1_mask_extraction_probe::field::QM31> for aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::composition_parts::closure#2<'_0>}]
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 1259:64-1259:106 -/
@[reducible]
def
  pool_v1.pair_forest_semantic_terminal.composition_parts.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeQM31
  : core.ops.function.FnMut
  pool_v1.pair_forest_semantic_terminal.composition_parts.closure_2 Std.Usize
  field.QM31 := {
  FnOnceInst :=
    pool_v1.pair_forest_semantic_terminal.composition_parts.closure_2.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31
  call_mut :=
    pool_v1.pair_forest_semantic_terminal.composition_parts.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
}

/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::composition_parts::{impl core::ops::function::FnMut<(usize,), aspis_r1_mask_extraction_probe::field::QM31> for aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::composition_parts::closure#1<'_0>}::call_mut]:
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 1258:63-1258:105 -/
def
  pool_v1.pair_forest_semantic_terminal.composition_parts.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
  (c : pool_v1.pair_forest_semantic_terminal.composition_parts.closure_1)
  (tupled_args : Std.Usize) :
  Result (field.QM31 ×
    pool_v1.pair_forest_semantic_terminal.composition_parts.closure_1)
  := do
  let q ←
    pool_v1.pair_forest_semantic_terminal.selected_claim c 1#usize tupled_args
  ok (q, c)

/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::composition_parts::{impl core::ops::function::FnOnce<(usize,), aspis_r1_mask_extraction_probe::field::QM31> for aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::composition_parts::closure#1<'_0>}::call_once]:
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 1258:63-1258:105 -/
def
  pool_v1.pair_forest_semantic_terminal.composition_parts.closure_1.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31.call_once
  (c : pool_v1.pair_forest_semantic_terminal.composition_parts.closure_1)
  (i : Std.Usize) :
  Result field.QM31
  := do
  let (q, _) ←
    pool_v1.pair_forest_semantic_terminal.composition_parts.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
      c i
  ok q

/-- Trait implementation: [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::composition_parts::{impl core::ops::function::FnOnce<(usize,), aspis_r1_mask_extraction_probe::field::QM31> for aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::composition_parts::closure#1<'_0>}]
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 1258:63-1258:105 -/
@[reducible]
def
  pool_v1.pair_forest_semantic_terminal.composition_parts.closure_1.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31
  : core.ops.function.FnOnce
  pool_v1.pair_forest_semantic_terminal.composition_parts.closure_1 Std.Usize
  field.QM31 := {
  call_once :=
    pool_v1.pair_forest_semantic_terminal.composition_parts.closure_1.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31.call_once
}

/-- Trait implementation: [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::composition_parts::{impl core::ops::function::FnMut<(usize,), aspis_r1_mask_extraction_probe::field::QM31> for aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::composition_parts::closure#1<'_0>}]
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 1258:63-1258:105 -/
@[reducible]
def
  pool_v1.pair_forest_semantic_terminal.composition_parts.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeQM31
  : core.ops.function.FnMut
  pool_v1.pair_forest_semantic_terminal.composition_parts.closure_1 Std.Usize
  field.QM31 := {
  FnOnceInst :=
    pool_v1.pair_forest_semantic_terminal.composition_parts.closure_1.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31
  call_mut :=
    pool_v1.pair_forest_semantic_terminal.composition_parts.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
}

/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::composition_parts::{impl core::ops::function::FnMut<(usize,), aspis_r1_mask_extraction_probe::field::QM31> for aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::composition_parts::closure<'_0>}::call_mut]:
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 1257:58-1257:100 -/
def
  pool_v1.pair_forest_semantic_terminal.composition_parts.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
  (c : pool_v1.pair_forest_semantic_terminal.composition_parts.closure)
  (tupled_args : Std.Usize) :
  Result (field.QM31 ×
    pool_v1.pair_forest_semantic_terminal.composition_parts.closure)
  := do
  let q ←
    pool_v1.pair_forest_semantic_terminal.selected_claim c 0#usize tupled_args
  ok (q, c)

/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::composition_parts::{impl core::ops::function::FnOnce<(usize,), aspis_r1_mask_extraction_probe::field::QM31> for aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::composition_parts::closure<'_0>}::call_once]:
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 1257:58-1257:100 -/
def
  pool_v1.pair_forest_semantic_terminal.composition_parts.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31.call_once
  (c : pool_v1.pair_forest_semantic_terminal.composition_parts.closure)
  (i : Std.Usize) :
  Result field.QM31
  := do
  let (q, _) ←
    pool_v1.pair_forest_semantic_terminal.composition_parts.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
      c i
  ok q

/-- Trait implementation: [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::composition_parts::{impl core::ops::function::FnOnce<(usize,), aspis_r1_mask_extraction_probe::field::QM31> for aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::composition_parts::closure<'_0>}]
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 1257:58-1257:100 -/
@[reducible]
def
  pool_v1.pair_forest_semantic_terminal.composition_parts.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31
  : core.ops.function.FnOnce
  pool_v1.pair_forest_semantic_terminal.composition_parts.closure Std.Usize
  field.QM31 := {
  call_once :=
    pool_v1.pair_forest_semantic_terminal.composition_parts.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31.call_once
}

/-- Trait implementation: [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::composition_parts::{impl core::ops::function::FnMut<(usize,), aspis_r1_mask_extraction_probe::field::QM31> for aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::composition_parts::closure<'_0>}]
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 1257:58-1257:100 -/
@[reducible]
def
  pool_v1.pair_forest_semantic_terminal.composition_parts.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31
  : core.ops.function.FnMut
  pool_v1.pair_forest_semantic_terminal.composition_parts.closure Std.Usize
  field.QM31 := {
  FnOnceInst :=
    pool_v1.pair_forest_semantic_terminal.composition_parts.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31
  call_mut :=
    pool_v1.pair_forest_semantic_terminal.composition_parts.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
}

/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::copy_variant]:
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 1208:0-1213:1 -/
def pool_v1.pair_forest_semantic_terminal.copy_variant
  (variant : pool_v1.pair_forest_semantic_terminal.CompiledVariant) :
  Result pool_v1.pair_forest_copy_terminal.PoolV1PairForestCompiledVariantV1
  := do
  match variant with
  | pool_v1.pair_forest_semantic_terminal.CompiledVariant.PrivateTransfer =>
    ok
      pool_v1.pair_forest_copy_terminal.PoolV1PairForestCompiledVariantV1.PrivateTransfer
  | pool_v1.pair_forest_semantic_terminal.CompiledVariant.Withdrawal =>
    ok
      pool_v1.pair_forest_copy_terminal.PoolV1PairForestCompiledVariantV1.Withdrawal
end AspisR1SelectedMaskProbe
