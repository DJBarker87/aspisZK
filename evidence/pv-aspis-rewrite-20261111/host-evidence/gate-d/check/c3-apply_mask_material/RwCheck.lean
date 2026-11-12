import ProverPin2.Funs
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048

namespace ProverPin2
namespace RW
noncomputable section

-- block emitted by tool k2 (7271db7e), sha256 7705c3887e7a9c6afe6bc08d567b5e792fbb6b8d395d40909b0c8282bed0be36, source ['/home/dombarker/project-offloads/codex-pv-aspis-rewrite-20261111/src-rw/crates/aspis-prover/src/state_only_hiding.rs', 245, 251]
def aspis_prover.state_only_hiding.inactive_m31_sum_except_step
  (sum : aspis_core.field.M31) (is_active : Bool) (row : Std.Usize)
  (dependent : Std.Usize) (table : Slice aspis_core.field.M31) :
  Result aspis_core.field.M31
  := do
  if is_active
  then ok sum
  else
    if row != dependent
    then let m ← Slice.index_usize table row
         aspis_core.field.M31.add sum m
    else ok sum

-- block emitted by tool k2 (7271db7e), sha256 9f634b42a82a69c46eb63658b797f0645526576e7c8fc6b7f0b990c1fb0c5fba, source ['/home/dombarker/project-offloads/codex-pv-aspis-rewrite-20261111/src-rw/crates/aspis-prover/src/state_only_hiding.rs', 235, 238]
def aspis_prover.state_only_hiding.inactive_m31_sum_except_loop.body
  (table : Slice aspis_core.field.M31) (active : Array Bool 1024#usize)
  (dependent : Std.Usize) (sum : aspis_core.field.M31) (row : Std.Usize) :
  Result (ControlFlow (aspis_core.field.M31 × Std.Usize) aspis_core.field.M31)
  := do
  let i ← aspis_statement.state_only_poseidon.STATE_ONLY_POSEIDON_TRACE_ROWS
  if row < i
  then
    let b ← Array.index_usize active row
    let sum1 ←
      aspis_prover.state_only_hiding.inactive_m31_sum_except_step sum b row
        dependent table
    let row1 ← lift (Std.Usize.wrapping_add row 1#usize)
    ok (cont (sum1, row1))
  else ok (done sum)

-- block emitted by tool k2 (7271db7e), sha256 53004a02c0632441eb48284099fbd671be30bc43d717d31160c34ae83c1e7243, source ['/home/dombarker/project-offloads/codex-pv-aspis-rewrite-20261111/src-rw/crates/aspis-prover/src/state_only_hiding.rs', 235, 238]
def aspis_prover.state_only_hiding.inactive_m31_sum_except_loop
  (table : Slice aspis_core.field.M31) (active : Array Bool 1024#usize)
  (dependent : Std.Usize) (sum : aspis_core.field.M31) (row : Std.Usize) :
  Result aspis_core.field.M31
  := do
  loop
    (fun (sum1, row1) =>
      aspis_prover.state_only_hiding.inactive_m31_sum_except_loop.body table
      active dependent sum1 row1)
    (sum, row)

-- block emitted by tool k2 (7271db7e), sha256 492643d7bc5e415c78bd78635dc604be8fcd35a93c6a442d01bd1b909bd929d6, source ['/home/dombarker/project-offloads/codex-pv-aspis-rewrite-20261111/src-rw/crates/aspis-prover/src/state_only_hiding.rs', 228, 232]
def aspis_prover.state_only_hiding.inactive_m31_sum_except
  (table : Slice aspis_core.field.M31) (active : Array Bool 1024#usize)
  (dependent : Std.Usize) :
  Result aspis_core.field.M31
  := do
  aspis_prover.state_only_hiding.inactive_m31_sum_except_loop table active
    dependent aspis_core.field.M31.ZERO 0#usize

-- block emitted by tool k2 (7271db7e), sha256 c45f9cd89cf3645324d4fda2594162a7b439efec09b5681155fc35d98b6ddb38, source ['/home/dombarker/project-offloads/codex-pv-aspis-rewrite-20261111/src-rw/crates/aspis-prover/src/state_only_hiding.rs', 209, 213]
def aspis_prover.state_only_hiding.balance_m31_copy_inactive
  (table : Slice aspis_core.field.M31) (dependent : Std.Usize)
  (active : Array Bool 1024#usize) :
  Result ((core.result.Result Unit
    aspis_prover.state_only_hiding.StateOnlyMaskBuildError) × (Slice
    aspis_core.field.M31))
  := do
  let i := Slice.len table
  let i1 ← aspis_statement.state_only_poseidon.STATE_ONLY_POSEIDON_TRACE_ROWS
  if i != i1
  then
    ok (core.result.Result.Err
      aspis_prover.state_only_hiding.StateOnlyMaskBuildError.TraceShape, table)
  else
    let b ← Array.index_usize active dependent
    if b
    then
      ok (core.result.Result.Err
        aspis_prover.state_only_hiding.StateOnlyMaskBuildError.TraceShape,
        table)
    else
      let sum ←
        aspis_prover.state_only_hiding.inactive_m31_sum_except table active
          dependent
      let m ← aspis_core.field.M31.sub aspis_core.field.M31.ZERO sum
      let table1 ← Slice.update table dependent m
      ok (core.result.Result.Ok (), table1)

-- block emitted by tool k2 (7271db7e), sha256 6a24c3067edeb2db1d9f1aea2487269d3836b6eed943df108d75e35ea8c32856, source ['/home/dombarker/project-offloads/codex-pv-aspis-rewrite-20261111/src-rw/crates/aspis-prover/src/state_only_hiding.rs', 1086, 1090]
def aspis_prover.state_only_hiding.inactive_dependent_rows_step
  (inactive_dependents : Array (Option Std.Usize) 16#usize)
  (cell : aspis_statement.trace_v4.TraceCell) (active : Array Bool 1024#usize)
  :
  Result (Array (Option Std.Usize) 16#usize)
  := do
  let row ← lift (core.convert.num.FromUsizeU16.from cell.row)
  let column ← lift (core.convert.num.FromUsizeU8.from cell.column)
  let b ← Array.index_usize active row
  if b
  then ok inactive_dependents
  else Array.update inactive_dependents column (some row)

-- block emitted by tool k2 (7271db7e), sha256 dd59eb5766453a129333f88666998d8919e0f76d6d2af9e8cb3be395a5eca1be, source ['/home/dombarker/project-offloads/codex-pv-aspis-rewrite-20261111/src-rw/crates/aspis-prover/src/state_only_hiding.rs', 1076, 1079]
def aspis_prover.state_only_hiding.inactive_dependent_rows_loop.body
  (cells : Slice aspis_statement.trace_v4.TraceCell)
  (active : Array Bool 1024#usize)
  (inactive_dependents : Array (Option Std.Usize) 16#usize) (index : Std.Usize)
  :
  Result (ControlFlow ((Array (Option Std.Usize) 16#usize) × Std.Usize) (Array
    (Option Std.Usize) 16#usize))
  := do
  let i := Slice.len cells
  if index < i
  then
    let tc ← Slice.index_usize cells index
    let inactive_dependents1 ←
      aspis_prover.state_only_hiding.inactive_dependent_rows_step
        inactive_dependents tc active
    let index1 ← lift (Std.Usize.wrapping_add index 1#usize)
    ok (cont (inactive_dependents1, index1))
  else ok (done inactive_dependents)

-- block emitted by tool k2 (7271db7e), sha256 845d02000bb0c397986862c61e0972cc481470532ab03b26a8a60ac82607603d, source ['/home/dombarker/project-offloads/codex-pv-aspis-rewrite-20261111/src-rw/crates/aspis-prover/src/state_only_hiding.rs', 1076, 1079]
def aspis_prover.state_only_hiding.inactive_dependent_rows_loop
  (cells : Slice aspis_statement.trace_v4.TraceCell)
  (active : Array Bool 1024#usize)
  (inactive_dependents : Array (Option Std.Usize) 16#usize) (index : Std.Usize)
  :
  Result (Array (Option Std.Usize) 16#usize)
  := do
  loop
    (fun (inactive_dependents1, index1) =>
      aspis_prover.state_only_hiding.inactive_dependent_rows_loop.body cells
      active inactive_dependents1 index1)
    (inactive_dependents, index)

-- block emitted by tool k2 (7271db7e), sha256 1763bd3c3f7f89df51e15d6de085fd6d6f3029b8ab64ce1d8d24d00ca2470712, source ['/home/dombarker/project-offloads/codex-pv-aspis-rewrite-20261111/src-rw/crates/aspis-prover/src/state_only_hiding.rs', 1070, 1073]
def aspis_prover.state_only_hiding.inactive_dependent_rows
  (cells : Slice aspis_statement.trace_v4.TraceCell)
  (active : Array Bool 1024#usize) :
  Result (Array (Option Std.Usize) 16#usize)
  := do
  let inactive_dependents := Array.repeat 16#usize none
  aspis_prover.state_only_hiding.inactive_dependent_rows_loop cells active
    inactive_dependents 0#usize

-- block emitted by tool k2 (7271db7e), sha256 6090b1e990410a42953ef4ab040227161d15d1ab1b8e726896920a0543407891, source ['/home/dombarker/project-offloads/codex-pv-aspis-rewrite-20261111/src-rw/crates/aspis-prover/src/state_only_hiding.rs', 1133, 1133]
def aspis_prover.state_only_hiding.add_cell_mask
  (trace : aspis_statement.state_only_trace.StateOnlyTraceFoundation)
  (cell : aspis_statement.trace_v4.TraceCell) (mask : aspis_core.field.M31) :
  Result aspis_statement.state_only_trace.StateOnlyTraceFoundation
  := do
  let column ← lift (core.convert.num.FromUsizeU8.from cell.column)
  let row ← lift (core.convert.num.FromUsizeU16.from cell.row)
  let v ← Array.index_usize trace.c1 column
  let m ←
    alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
      aspis_core.field.M31) v row
  let m1 ← aspis_core.field.M31.add m mask
  let (v1, index_mut_back) ← Array.index_mut_usize trace.c1 column
  let (_, index_mut_back1) ←
    alloc.vec.Vec.index_mut (core.slice.index.SliceIndexUsizeSlice
      aspis_core.field.M31) v1 row
  let v2 := index_mut_back1 m1
  let a := index_mut_back v2
  ok { c1 := a }

-- block emitted by tool k2 (7271db7e), sha256 1bbdb048b73fb2e5ea12ad03adf919d1c7ff8a621740d0a055d700d394e676f7, source ['/home/dombarker/project-offloads/codex-pv-aspis-rewrite-20261111/src-rw/crates/aspis-prover/src/state_only_hiding.rs', 1107, 1110]
def aspis_prover.state_only_hiding.add_cell_masks_loop.body
  (cells : Slice aspis_statement.trace_v4.TraceCell)
  (masks : alloc.vec.Vec aspis_core.field.M31)
  (trace : aspis_statement.state_only_trace.StateOnlyTraceFoundation)
  (index : Std.Usize) :
  Result (ControlFlow
    (aspis_statement.state_only_trace.StateOnlyTraceFoundation × Std.Usize)
    aspis_statement.state_only_trace.StateOnlyTraceFoundation)
  := do
  let i := Slice.len cells
  if index < i
  then
    let tc ← Slice.index_usize cells index
    let m ←
      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
        aspis_core.field.M31) masks index
    let trace1 ← aspis_prover.state_only_hiding.add_cell_mask trace tc m
    let index1 ← lift (Std.Usize.wrapping_add index 1#usize)
    ok (cont (trace1, index1))
  else ok (done trace)

-- block emitted by tool k2 (7271db7e), sha256 3d73ba9761e2281a3648b413800ea9a0a4bc9019572551ab6c6643eda485497a, source ['/home/dombarker/project-offloads/codex-pv-aspis-rewrite-20261111/src-rw/crates/aspis-prover/src/state_only_hiding.rs', 1107, 1110]
def aspis_prover.state_only_hiding.add_cell_masks_loop
  (trace : aspis_statement.state_only_trace.StateOnlyTraceFoundation)
  (cells : Slice aspis_statement.trace_v4.TraceCell)
  (masks : alloc.vec.Vec aspis_core.field.M31) (index : Std.Usize) :
  Result aspis_statement.state_only_trace.StateOnlyTraceFoundation
  := do
  loop
    (fun (trace1, index1) =>
      aspis_prover.state_only_hiding.add_cell_masks_loop.body cells masks
      trace1 index1)
    (trace, index)

-- block emitted by tool k2 (7271db7e), sha256 d993b9454012aa7b869194d311fc70fb21201a6c0af63ad422f05aa7fa49dc3a, source ['/home/dombarker/project-offloads/codex-pv-aspis-rewrite-20261111/src-rw/crates/aspis-prover/src/state_only_hiding.rs', 1101, 1105]
def aspis_prover.state_only_hiding.add_cell_masks
  (trace : aspis_statement.state_only_trace.StateOnlyTraceFoundation)
  (cells : Slice aspis_statement.trace_v4.TraceCell)
  (masks : alloc.vec.Vec aspis_core.field.M31) :
  Result aspis_statement.state_only_trace.StateOnlyTraceFoundation
  := do
  aspis_prover.state_only_hiding.add_cell_masks_loop trace cells masks 0#usize

-- block emitted by tool k2 (7271db7e), sha256 ef0b3f9f53cb333b73b6822057323fd033cb55628cd95b791113374e9fa743fb, source ['/home/dombarker/project-offloads/codex-pv-aspis-rewrite-20261111/src-rw/crates/aspis-prover/src/state_only_hiding.rs', 1123, 1128]
def aspis_prover.state_only_hiding.balance_trace_columns_loop.body
  (dependents : Array (Option Std.Usize) 16#usize)
  (active : Array Bool 1024#usize)
  (trace : aspis_statement.state_only_trace.StateOnlyTraceFoundation)
  (column : Std.Usize) :
  Result (ControlFlow
    (aspis_statement.state_only_trace.StateOnlyTraceFoundation × Std.Usize)
    ((core.result.Result Unit
    aspis_prover.state_only_hiding.StateOnlyMaskBuildError) ×
    aspis_statement.state_only_trace.StateOnlyTraceFoundation))
  := do
  if column < aspis_core.state_only_hiding.STATE_ONLY_HIDING_C1_COLUMNS
  then
    let (v, index_mut_back) ← Array.index_mut_usize trace.c1 column
    let (s, deref_mut_back) ← lift (alloc.vec.Vec.deref_mut v)
    let o ← Array.index_usize dependents column
    let i ← core.option.Option.unwrap o
    let (r, s1) ←
      aspis_prover.state_only_hiding.balance_m31_copy_inactive s i active
    let cf ← core.result.Result.Insts.CoreOpsTry.branch r
    match cf with
    | core.ops.control_flow.ControlFlow.Continue _ =>
      let column1 ← lift (Std.Usize.wrapping_add column 1#usize)
      let v1 := deref_mut_back s1
      let a := index_mut_back v1
      ok (cont ({ c1 := a }, column1))
    | core.ops.control_flow.ControlFlow.Break residual =>
      let r1 ←
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          Unit (core.convert.FromSame
          aspis_prover.state_only_hiding.StateOnlyMaskBuildError) residual
      let v1 := deref_mut_back s1
      let a := index_mut_back v1
      ok (done (r1, { c1 := a }))
  else ok (done (core.result.Result.Ok (), trace))

-- block emitted by tool k2 (7271db7e), sha256 5a611bd8c0570db93e2df05f412afc155c68f6043c1bf3415845f1d2211d22e1, source ['/home/dombarker/project-offloads/codex-pv-aspis-rewrite-20261111/src-rw/crates/aspis-prover/src/state_only_hiding.rs', 1123, 1128]
def aspis_prover.state_only_hiding.balance_trace_columns_loop
  (trace : aspis_statement.state_only_trace.StateOnlyTraceFoundation)
  (dependents : Array (Option Std.Usize) 16#usize)
  (active : Array Bool 1024#usize) (column : Std.Usize) :
  Result ((core.result.Result Unit
    aspis_prover.state_only_hiding.StateOnlyMaskBuildError) ×
    aspis_statement.state_only_trace.StateOnlyTraceFoundation)
  := do
  loop
    (fun (trace1, column1) =>
      aspis_prover.state_only_hiding.balance_trace_columns_loop.body dependents
      active trace1 column1)
    (trace, column)

-- block emitted by tool k2 (7271db7e), sha256 337e569161052574d6b1ed7cf887382630dbb14f3acf53653525bf9c6d04f61a, source ['/home/dombarker/project-offloads/codex-pv-aspis-rewrite-20261111/src-rw/crates/aspis-prover/src/state_only_hiding.rs', 1117, 1121]
def aspis_prover.state_only_hiding.balance_trace_columns
  (trace : aspis_statement.state_only_trace.StateOnlyTraceFoundation)
  (dependents : Array (Option Std.Usize) 16#usize)
  (active : Array Bool 1024#usize) :
  Result ((core.result.Result Unit
    aspis_prover.state_only_hiding.StateOnlyMaskBuildError) ×
    aspis_statement.state_only_trace.StateOnlyTraceFoundation)
  := do
  aspis_prover.state_only_hiding.balance_trace_columns_loop trace dependents
    active 0#usize

-- block emitted by tool k2 (7271db7e), sha256 9e0e97402ba941fdc997e943064a88869daab45c03b9747cd08b44ed922df781, source ['/home/dombarker/project-offloads/codex-pv-aspis-rewrite-20261111/src-rw/crates/aspis-prover/src/state_only_hiding.rs', 1176, 1176]
def
  aspis_prover.state_only_hiding.apply_mask_material_for_layout.closure_2.Insts.CoreOpsFunctionFnOnceTupleSharedOptionUsizeBool.call_once
  (c : aspis_prover.state_only_hiding.apply_mask_material_for_layout.closure_2)
  (o : Option Std.Usize) :
  Result Bool
  := do
  let (b, _) ←
    aspis_prover.state_only_hiding.apply_mask_material_for_layout.closure_2.Insts.CoreOpsFunctionFnMutTupleSharedOptionUsizeBool.call_mut
      c o
  ok b

-- block emitted by tool k2 (7271db7e), sha256 b2d1c98c7e0e555bbc46abc2a18753c66f5457dd23cb9ca3e76206bd08d1e79a, source ['/home/dombarker/project-offloads/codex-pv-aspis-rewrite-20261111/src-rw/crates/aspis-prover/src/state_only_hiding.rs', 1176, 1176]
def
  aspis_prover.state_only_hiding.apply_mask_material_for_layout.closure_2.Insts.CoreOpsFunctionFnOnceTupleSharedOptionUsizeBool
  : core.ops.function.FnOnce
  aspis_prover.state_only_hiding.apply_mask_material_for_layout.closure_2
  (Option Std.Usize) Bool := {
  call_once :=
    aspis_prover.state_only_hiding.apply_mask_material_for_layout.closure_2.Insts.CoreOpsFunctionFnOnceTupleSharedOptionUsizeBool.call_once
}

-- block emitted by tool k2 (7271db7e), sha256 405bf8104b06261a5930e7f5264d4e1f39e2bf0e6a9721aeda3b1254c53b6b47, source ['/home/dombarker/project-offloads/codex-pv-aspis-rewrite-20261111/src-rw/crates/aspis-prover/src/state_only_hiding.rs', 1176, 1176]
def
  aspis_prover.state_only_hiding.apply_mask_material_for_layout.closure_2.Insts.CoreOpsFunctionFnMutTupleSharedOptionUsizeBool
  : core.ops.function.FnMut
  aspis_prover.state_only_hiding.apply_mask_material_for_layout.closure_2
  (Option Std.Usize) Bool := {
  FnOnceInst :=
    aspis_prover.state_only_hiding.apply_mask_material_for_layout.closure_2.Insts.CoreOpsFunctionFnOnceTupleSharedOptionUsizeBool
  call_mut :=
    aspis_prover.state_only_hiding.apply_mask_material_for_layout.closure_2.Insts.CoreOpsFunctionFnMutTupleSharedOptionUsizeBool.call_mut
}

-- block emitted by tool k2 (7271db7e), sha256 48648c1e6aa08e99e538106837fa50b8b6c58f66b45d7708b31569ee254c33a2, source ['/home/dombarker/project-offloads/codex-pv-aspis-rewrite-20261111/src-rw/crates/aspis-prover/src/state_only_hiding.rs', 1162, 1162]
def
  aspis_prover.state_only_hiding.apply_mask_material_for_layout.closure_1.Insts.CoreOpsFunctionFnOnceTupleSharedVecM31Bool.call_once
  (c : aspis_prover.state_only_hiding.apply_mask_material_for_layout.closure_1)
  (v : alloc.vec.Vec aspis_core.field.M31) :
  Result Bool
  := do
  let (b, _) ←
    aspis_prover.state_only_hiding.apply_mask_material_for_layout.closure_1.Insts.CoreOpsFunctionFnMutTupleSharedVecM31Bool.call_mut
      c v
  ok b

-- block emitted by tool k2 (7271db7e), sha256 fe50863c0684bfc634ad230e91b8462978fc9e611c0590f7ccc70dbac2efe203, source ['/home/dombarker/project-offloads/codex-pv-aspis-rewrite-20261111/src-rw/crates/aspis-prover/src/state_only_hiding.rs', 1162, 1162]
def
  aspis_prover.state_only_hiding.apply_mask_material_for_layout.closure_1.Insts.CoreOpsFunctionFnOnceTupleSharedVecM31Bool
  : core.ops.function.FnOnce
  aspis_prover.state_only_hiding.apply_mask_material_for_layout.closure_1
  (alloc.vec.Vec aspis_core.field.M31) Bool := {
  call_once :=
    aspis_prover.state_only_hiding.apply_mask_material_for_layout.closure_1.Insts.CoreOpsFunctionFnOnceTupleSharedVecM31Bool.call_once
}

-- block emitted by tool k2 (7271db7e), sha256 54e6312a4b4f1a663c9be58c0231f7398e0a98df3836c59d9b9a0bd63f4eb292, source ['/home/dombarker/project-offloads/codex-pv-aspis-rewrite-20261111/src-rw/crates/aspis-prover/src/state_only_hiding.rs', 1162, 1162]
def
  aspis_prover.state_only_hiding.apply_mask_material_for_layout.closure_1.Insts.CoreOpsFunctionFnMutTupleSharedVecM31Bool
  : core.ops.function.FnMut
  aspis_prover.state_only_hiding.apply_mask_material_for_layout.closure_1
  (alloc.vec.Vec aspis_core.field.M31) Bool := {
  FnOnceInst :=
    aspis_prover.state_only_hiding.apply_mask_material_for_layout.closure_1.Insts.CoreOpsFunctionFnOnceTupleSharedVecM31Bool
  call_mut :=
    aspis_prover.state_only_hiding.apply_mask_material_for_layout.closure_1.Insts.CoreOpsFunctionFnMutTupleSharedVecM31Bool.call_mut
}

-- block emitted by tool k2 (7271db7e), sha256 b05c3a872851ae46bc7649da8678980ebe00a67cfa4476a513bba75e7d61d98e, source ['/home/dombarker/project-offloads/codex-pv-aspis-rewrite-20261111/src-rw/crates/aspis-prover/src/state_only_hiding.rs', 1154, 1154]
def
  aspis_prover.state_only_hiding.apply_mask_material_for_layout.closure.Insts.CoreOpsFunctionFnOnceTupleSharedVecM31Bool.call_once
  (c : aspis_prover.state_only_hiding.apply_mask_material_for_layout.closure)
  (v : alloc.vec.Vec aspis_core.field.M31) :
  Result Bool
  := do
  let (b, _) ←
    aspis_prover.state_only_hiding.apply_mask_material_for_layout.closure.Insts.CoreOpsFunctionFnMutTupleSharedVecM31Bool.call_mut
      c v
  ok b

-- block emitted by tool k2 (7271db7e), sha256 b5004f7d68b981c6988dcedc2616de6a0d2fcdfe322d6277bb9cc1c4f4e4cb4d, source ['/home/dombarker/project-offloads/codex-pv-aspis-rewrite-20261111/src-rw/crates/aspis-prover/src/state_only_hiding.rs', 1154, 1154]
def
  aspis_prover.state_only_hiding.apply_mask_material_for_layout.closure.Insts.CoreOpsFunctionFnOnceTupleSharedVecM31Bool
  : core.ops.function.FnOnce
  aspis_prover.state_only_hiding.apply_mask_material_for_layout.closure
  (alloc.vec.Vec aspis_core.field.M31) Bool := {
  call_once :=
    aspis_prover.state_only_hiding.apply_mask_material_for_layout.closure.Insts.CoreOpsFunctionFnOnceTupleSharedVecM31Bool.call_once
}

-- block emitted by tool k2 (7271db7e), sha256 57261300fa68a29a087ec6680ce338f27e7452b46bd8a4399dc713f760e94263, source ['/home/dombarker/project-offloads/codex-pv-aspis-rewrite-20261111/src-rw/crates/aspis-prover/src/state_only_hiding.rs', 1154, 1154]
def
  aspis_prover.state_only_hiding.apply_mask_material_for_layout.closure.Insts.CoreOpsFunctionFnMutTupleSharedVecM31Bool
  : core.ops.function.FnMut
  aspis_prover.state_only_hiding.apply_mask_material_for_layout.closure
  (alloc.vec.Vec aspis_core.field.M31) Bool := {
  FnOnceInst :=
    aspis_prover.state_only_hiding.apply_mask_material_for_layout.closure.Insts.CoreOpsFunctionFnOnceTupleSharedVecM31Bool
  call_mut :=
    aspis_prover.state_only_hiding.apply_mask_material_for_layout.closure.Insts.CoreOpsFunctionFnMutTupleSharedVecM31Bool.call_mut
}

-- block emitted by tool k2 (7271db7e), sha256 eeb20d020796b3c4262877cf4a74778de0bd44cbe43e5b630b20bed1662a9d08, source ['/home/dombarker/project-offloads/codex-pv-aspis-rewrite-20261111/src-rw/crates/aspis-prover/src/state_only_hiding.rs', 1145, 1150]
def aspis_prover.state_only_hiding.apply_mask_material_for_layout
  (trace : aspis_statement.state_only_trace.StateOnlyTraceFoundation)
  (material : aspis_prover.state_only_hiding.StateOnlyMaskMaterial)
  (cells : Slice aspis_statement.trace_v4.TraceCell)
  (active : Array Bool 1024#usize) :
  Result ((core.result.Result
    aspis_prover.state_only_hiding.AppliedStateOnlyMasks
    aspis_prover.state_only_hiding.StateOnlyMaskBuildError) ×
    aspis_statement.state_only_trace.StateOnlyTraceFoundation)
  := do
  let s ← lift (Array.to_slice trace.c1)
  let i ← core.slice.Slice.iter s
  let (b, _) ←
    core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.any
      aspis_prover.state_only_hiding.apply_mask_material_for_layout.closure.Insts.CoreOpsFunctionFnMutTupleSharedVecM31Bool
      i ()
  if b
  then
    ok (core.result.Result.Err
      aspis_prover.state_only_hiding.StateOnlyMaskBuildError.TraceShape, trace)
  else
    let i1 := alloc.vec.Vec.len material.c1
    let i2 := Slice.len cells
    if i1 != i2
    then
      ok (core.result.Result.Err
        aspis_prover.state_only_hiding.StateOnlyMaskBuildError.TraceShape,
        trace)
    else
      let s1 ← lift (Array.to_slice material.mask_only_c1)
      let i3 ← core.slice.Slice.iter s1
      let (b1, _) ←
        core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.any
          aspis_prover.state_only_hiding.apply_mask_material_for_layout.closure_1.Insts.CoreOpsFunctionFnMutTupleSharedVecM31Bool
          i3 ()
      if b1
      then
        ok (core.result.Result.Err
          aspis_prover.state_only_hiding.StateOnlyMaskBuildError.TraceShape,
          trace)
      else
        let i4 := alloc.vec.Vec.len material.g
        let i5 ←
          aspis_statement.state_only_poseidon.STATE_ONLY_POSEIDON_TRACE_ROWS
        if i4 != i5
        then
          ok (core.result.Result.Err
            aspis_prover.state_only_hiding.StateOnlyMaskBuildError.TraceShape,
            trace)
        else
          let i6 := alloc.vec.Vec.len material.h1_padding
          if i6 != i5
          then
            ok (core.result.Result.Err
              aspis_prover.state_only_hiding.StateOnlyMaskBuildError.TraceShape,
              trace)
          else
            let inactive_dependents ←
              aspis_prover.state_only_hiding.inactive_dependent_rows cells
                active
            let s2 ← lift (Array.to_slice inactive_dependents)
            let i7 ← core.slice.Slice.iter s2
            let (b2, _) ←
              core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.any
                aspis_prover.state_only_hiding.apply_mask_material_for_layout.closure_2.Insts.CoreOpsFunctionFnMutTupleSharedOptionUsizeBool
                i7 ()
            if b2
            then
              ok (core.result.Result.Err
                aspis_prover.state_only_hiding.StateOnlyMaskBuildError.Layout,
                trace)
            else
              let (v, _) ←
                core.mem.take (alloc.vec.Vec.Insts.CoreDefaultDefault
                  aspis_core.field.M31) material.c1
              let trace1 ←
                aspis_prover.state_only_hiding.add_cell_masks trace cells v
              let (r, trace2) ←
                aspis_prover.state_only_hiding.balance_trace_columns trace1
                  inactive_dependents active
              let cf ← core.result.Result.Insts.CoreOpsTry.branch r
              match cf with
              | core.ops.control_flow.ControlFlow.Continue _ =>
                let (a, _) ←
                  core.mem.take (core.default.DefaultArray 10#usize
                    (alloc.vec.Vec.Insts.CoreDefaultDefault
                    aspis_core.field.M31)) material.mask_only_c1
                let (v1, _) ←
                  core.mem.take (alloc.vec.Vec.Insts.CoreDefaultDefault
                    aspis_core.field.QM31) material.g
                let (v2, _) ←
                  core.mem.take (alloc.vec.Vec.Insts.CoreDefaultDefault
                    aspis_core.field.QM31) material.h1_padding
                ok (core.result.Result.Ok
                  {
                    mask_only_c1 := a,
                    g := v1,
                    h1_padding := v2,
                    mask_nonce := material.mask_nonce
                  }, trace2)
              | core.ops.control_flow.ControlFlow.Break residual =>
                let r1 ←
                  core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                    aspis_prover.state_only_hiding.AppliedStateOnlyMasks
                    (core.convert.FromSame
                    aspis_prover.state_only_hiding.StateOnlyMaskBuildError)
                    residual
                ok (r1, trace2)

end
end RW
end ProverPin2

#check @ProverPin2.RW.aspis_prover.state_only_hiding.inactive_dependent_rows_step
#print axioms ProverPin2.RW.aspis_prover.state_only_hiding.inactive_dependent_rows_step
#check @ProverPin2.RW.aspis_prover.state_only_hiding.inactive_dependent_rows
#print axioms ProverPin2.RW.aspis_prover.state_only_hiding.inactive_dependent_rows
#check @ProverPin2.RW.aspis_prover.state_only_hiding.add_cell_mask
#print axioms ProverPin2.RW.aspis_prover.state_only_hiding.add_cell_mask
#check @ProverPin2.RW.aspis_prover.state_only_hiding.add_cell_masks
#print axioms ProverPin2.RW.aspis_prover.state_only_hiding.add_cell_masks
#check @ProverPin2.RW.aspis_prover.state_only_hiding.balance_trace_columns
#print axioms ProverPin2.RW.aspis_prover.state_only_hiding.balance_trace_columns
#check @ProverPin2.RW.aspis_prover.state_only_hiding.inactive_m31_sum_except_step
#print axioms ProverPin2.RW.aspis_prover.state_only_hiding.inactive_m31_sum_except_step
#check @ProverPin2.RW.aspis_prover.state_only_hiding.inactive_m31_sum_except
#print axioms ProverPin2.RW.aspis_prover.state_only_hiding.inactive_m31_sum_except
example : type_of% @ProverPin2.RW.aspis_prover.state_only_hiding.balance_m31_copy_inactive = type_of% @ProverPin2.aspis_prover.state_only_hiding.balance_m31_copy_inactive := rfl
#check @ProverPin2.RW.aspis_prover.state_only_hiding.balance_m31_copy_inactive
#print axioms ProverPin2.RW.aspis_prover.state_only_hiding.balance_m31_copy_inactive
example : type_of% @ProverPin2.RW.aspis_prover.state_only_hiding.apply_mask_material_for_layout = type_of% @aspis_prover.state_only_hiding.apply_mask_material_for_layout := rfl
#check @ProverPin2.RW.aspis_prover.state_only_hiding.apply_mask_material_for_layout
#print axioms ProverPin2.RW.aspis_prover.state_only_hiding.apply_mask_material_for_layout
-- 26 carried blocks, 0 new opaque items, 2 signature checks
