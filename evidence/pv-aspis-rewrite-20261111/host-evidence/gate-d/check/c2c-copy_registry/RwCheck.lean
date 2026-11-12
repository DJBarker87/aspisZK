import ProverPin2.Funs
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048

namespace ProverPin2
namespace RW
noncomputable section

-- block emitted by tool k2 (7271db7e), sha256 c8bc80c63168b5a5b715778374400c8637e69c97fd34349109ff844a2a463c35, source ['/home/dombarker/project-offloads/codex-pv-aspis-rewrite-20261111/src-rw/crates/aspis-statement/src/pool_v1/pair_tree_hiding.rs', 255, 268]
def aspis_statement.pool_v1.pair_tree_hiding.endpoint_counts_loop.body
  (iter : core.slice.iter.Iter
  aspis_statement.pool_v1.pair_tree_hiding.PoolV1PairCopyRowLinkV1)
  (producers : Array Std.U8 1024#usize) (consumers : Array Std.U8 1024#usize) :
  Result (ControlFlow ((core.slice.iter.Iter
    aspis_statement.pool_v1.pair_tree_hiding.PoolV1PairCopyRowLinkV1) × (Array
    Std.U8 1024#usize) × (Array Std.U8 1024#usize)) (core.result.Result
    ((Array Std.U8 1024#usize) × (Array Std.U8 1024#usize))
    aspis_statement.pool_v1.pair_tree_hiding.PoolV1PairHidingLayoutErrorV1))
  := do
  let (o, iter1) ← core.slice.iter.IteratorSliceIter.next iter
  match o with
  | none => ok (done (core.result.Result.Ok (producers, consumers)))
  | some link =>
    let row ← lift (core.convert.num.FromUsizeU16.from link.producer_row)
    let i ← aspis_statement.pool_v1.pair_tree_profile.POOL_V1_PAIR_TRACE_ROWS
    if row >= i
    then
      let i1 ← lift (UScalar.cast .U16 row)
      ok (done (core.result.Result.Err
        (aspis_statement.pool_v1.pair_tree_hiding.PoolV1PairHidingLayoutErrorV1.EndpointCapacity
        i1)))
    else
      let i1 ← Array.index_usize producers row
      if i1 >= 2#u8
      then
        let i2 ← lift (UScalar.cast .U16 row)
        ok (done (core.result.Result.Err
          (aspis_statement.pool_v1.pair_tree_hiding.PoolV1PairHidingLayoutErrorV1.EndpointCapacity
          i2)))
      else
        let i2 ← lift (Std.U8.wrapping_add i1 1#u8)
        let (_, index_mut_back) ← Array.index_mut_usize producers row
        let row1 ←
          lift (core.convert.num.FromUsizeU16.from link.consumer_row)
        if row1 >= i
        then
          let i3 ← lift (UScalar.cast .U16 row1)
          ok (done (core.result.Result.Err
            (aspis_statement.pool_v1.pair_tree_hiding.PoolV1PairHidingLayoutErrorV1.EndpointCapacity
            i3)))
        else
          let i3 ← Array.index_usize consumers row1
          if i3 >= 2#u8
          then
            let i4 ← lift (UScalar.cast .U16 row1)
            ok (done (core.result.Result.Err
              (aspis_statement.pool_v1.pair_tree_hiding.PoolV1PairHidingLayoutErrorV1.EndpointCapacity
              i4)))
          else
            let i4 ← lift (Std.U8.wrapping_add i3 1#u8)
            let a ← Array.update consumers row1 i4
            let a1 := index_mut_back i2
            ok (cont (iter1, a1, a))

-- block emitted by tool k2 (7271db7e), sha256 b4083b90051177ef140a21ecd191da1a3b636f35e065a6fae833ce3d757baed8, source ['/home/dombarker/project-offloads/codex-pv-aspis-rewrite-20261111/src-rw/crates/aspis-statement/src/pool_v1/pair_tree_hiding.rs', 255, 268]
def aspis_statement.pool_v1.pair_tree_hiding.endpoint_counts_loop
  (iter : core.slice.iter.Iter
  aspis_statement.pool_v1.pair_tree_hiding.PoolV1PairCopyRowLinkV1)
  (producers : Array Std.U8 1024#usize) (consumers : Array Std.U8 1024#usize) :
  Result (core.result.Result ((Array Std.U8 1024#usize) × (Array Std.U8
    1024#usize))
    aspis_statement.pool_v1.pair_tree_hiding.PoolV1PairHidingLayoutErrorV1)
  := do
  loop
    (fun (iter1, producers1, consumers1) =>
      aspis_statement.pool_v1.pair_tree_hiding.endpoint_counts_loop.body iter1
      producers1 consumers1)
    (iter, producers, consumers)

-- block emitted by tool k2 (7271db7e), sha256 854f2371c9416521fcf980d8c84229c8a0e012204b5fbd563cbe84f9be030095, source ['/home/dombarker/project-offloads/codex-pv-aspis-rewrite-20261111/src-rw/crates/aspis-statement/src/pool_v1/pair_tree_hiding.rs', 246, 248]
def aspis_statement.pool_v1.pair_tree_hiding.endpoint_counts
  (links : Slice
  aspis_statement.pool_v1.pair_tree_hiding.PoolV1PairCopyRowLinkV1) :
  Result (core.result.Result ((Array Std.U8 1024#usize) × (Array Std.U8
    1024#usize))
    aspis_statement.pool_v1.pair_tree_hiding.PoolV1PairHidingLayoutErrorV1)
  := do
  let producers := Array.repeat 1024#usize 0#u8
  let consumers := Array.repeat 1024#usize 0#u8
  let iter ←
    SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter
      links
  aspis_statement.pool_v1.pair_tree_hiding.endpoint_counts_loop iter producers
    consumers

-- block emitted by tool k2 (7271db7e), sha256 b6db4d526b1524e3556b1adc7941dfebb15dd986dc1fdbd2e8308d5b71bad0d9, source ['/home/dombarker/project-offloads/codex-pv-aspis-rewrite-20261111/src-rw/crates/aspis-statement/src/pool_v1/pair_tree_hiding.rs', 105, 106]
def
  aspis_statement.pool_v1.pair_tree_hiding.build_pool_v1_pair_copy_row_schedule_v1
  :
  Result (core.result.Result (alloc.vec.Vec
    aspis_statement.pool_v1.pair_tree_hiding.PoolV1PairCopyRowLinkV1)
    aspis_statement.pool_v1.pair_tree_hiding.PoolV1PairHidingLayoutErrorV1)
  := do
  let links :=
    alloc.vec.Vec.with_capacity
      aspis_statement.pool_v1.pair_tree_hiding.PoolV1PairCopyRowLinkV1
      aspis_statement.pool_v1.pair_tree_hiding.POOL_V1_PAIR_COPY_ROW_LINKS_V1
  let iter ←
    Array.Insts.CoreIterTraitsCollectIntoIteratorTIntoIter.into_iter
      (Array.make 7#usize [
        (1#usize, 2#usize), (2#usize, 3#usize), (25#usize, 26#usize),
        (27#usize, 28#usize), (28#usize, 29#usize), (30#usize, 31#usize),
        (31#usize, 32#usize)
        ])
  aspis_statement.pool_v1.pair_tree_hiding.build_pool_v1_pair_copy_row_schedule_v1_loop0
    iter links

-- block emitted by tool k2 (7271db7e), sha256 67848b19fe0c42bd2f42cad38474e650fa27fb763697229921e3d235ff4208e3, source ['/home/dombarker/project-offloads/codex-pv-aspis-rewrite-20261111/src-rw/crates/aspis-statement/src/pool_v1/pair_forest_trace.rs', 553, 560]
def aspis_statement.pool_v1.pair_forest_trace.first_link_of_kind_loop.body
  (legacy : Slice aspis_statement.pool_v1.pair_trace.PoolV1PairCopyLinkV1)
  (kind : aspis_statement.pool_v1.pair_tree_hiding.PoolV1PairCopyRowLinkKindV1)
  (index : Std.Usize) :
  Result (ControlFlow Std.Usize (Option Std.Usize))
  := do
  let i := Slice.len legacy
  if index < i
  then
    let pvpclv ← Slice.index_usize legacy index
    let b ←
      aspis_statement.pool_v1.pair_tree_hiding.PoolV1PairCopyRowLinkKindV1.Insts.CoreCmpPartialEqPoolV1PairCopyRowLinkKindV1.eq
        pvpclv.kind kind
    if b
    then ok (done (some index))
    else
      let index1 ← lift (Std.Usize.wrapping_add index 1#usize)
      ok (cont index1)
  else ok (done none)

-- block emitted by tool k2 (7271db7e), sha256 87862e4ad4380f9dfd7e624c6e4d80175b85d59cb9dacc48eb4c563251cb9155, source ['/home/dombarker/project-offloads/codex-pv-aspis-rewrite-20261111/src-rw/crates/aspis-statement/src/pool_v1/pair_forest_trace.rs', 553, 560]
def aspis_statement.pool_v1.pair_forest_trace.first_link_of_kind_loop
  (legacy : Slice aspis_statement.pool_v1.pair_trace.PoolV1PairCopyLinkV1)
  (kind : aspis_statement.pool_v1.pair_tree_hiding.PoolV1PairCopyRowLinkKindV1)
  (index : Std.Usize) :
  Result (Option Std.Usize)
  := do
  loop
    (fun index1 =>
      aspis_statement.pool_v1.pair_forest_trace.first_link_of_kind_loop.body
      legacy kind index1)
    index

-- block emitted by tool k2 (7271db7e), sha256 4dfd658003382e03f225736079be584104420fdc8ee852a69c0be28d78bb33fa, source ['/home/dombarker/project-offloads/codex-pv-aspis-rewrite-20261111/src-rw/crates/aspis-statement/src/pool_v1/pair_forest_trace.rs', 548, 551]
def aspis_statement.pool_v1.pair_forest_trace.first_link_of_kind
  (legacy : Slice aspis_statement.pool_v1.pair_trace.PoolV1PairCopyLinkV1)
  (kind : aspis_statement.pool_v1.pair_tree_hiding.PoolV1PairCopyRowLinkKindV1)
  :
  Result (Option Std.Usize)
  := do
  aspis_statement.pool_v1.pair_forest_trace.first_link_of_kind_loop legacy kind
    0#usize

-- block emitted by tool k2 (7271db7e), sha256 1a160abc16d07704a06665456d74f155d5d87e1748045c7f8b245dcb09fca363, source ['/home/dombarker/project-offloads/codex-pv-aspis-rewrite-20261111/src-rw/crates/aspis-statement/src/pool_v1/pair_trace.rs', 1052, 1053]
def aspis_statement.pool_v1.pair_trace.build_pool_v1_pair_copy_registry_v1
  :
  Result (core.result.Result (alloc.vec.Vec
    aspis_statement.pool_v1.pair_trace.PoolV1PairCopyLinkV1)
    aspis_statement.pool_v1.pair_trace.PoolV1PairTraceErrorV1)
  := do
  let r ←
    aspis_statement.pool_v1.pair_tree_hiding.build_pool_v1_pair_copy_row_schedule_v1
  let r1 ←
    core.result.Result.map_err
      aspis_statement.pool_v1.pair_trace.build_pool_v1_pair_copy_registry_v1.closure.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairHidingLayoutErrorV1PoolV1PairTraceErrorV1
      r ()
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r1
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let i := alloc.vec.Vec.len val
    let output :=
      alloc.vec.Vec.with_capacity
        aspis_statement.pool_v1.pair_trace.PoolV1PairCopyLinkV1 i
    let iter ← alloc.vec.IntoIteratorVec.into_iter val
    let output1 ←
      aspis_statement.pool_v1.pair_trace.build_pool_v1_pair_copy_registry_v1_loop
        iter output
    let i1 := alloc.vec.Vec.len output1
    if i1 !=
      aspis_statement.pool_v1.pair_tree_hiding.POOL_V1_PAIR_COPY_ROW_LINKS_V1
    then
      ok (core.result.Result.Err
        aspis_statement.pool_v1.pair_trace.PoolV1PairTraceErrorV1.CopyLayout)
    else ok (core.result.Result.Ok output1)
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      (alloc.vec.Vec aspis_statement.pool_v1.pair_trace.PoolV1PairCopyLinkV1)
      (core.convert.FromSame
      aspis_statement.pool_v1.pair_trace.PoolV1PairTraceErrorV1) residual

-- block emitted by tool k2 (7271db7e), sha256 e2de69c35561b5e42f639687fdb084b30b3d7f6f611797fbf514115b9673baf8, source ['/home/dombarker/project-offloads/codex-pv-aspis-rewrite-20261111/src-rw/crates/aspis-statement/src/pool_v1/pair_forest_trace.rs', 568, 617]
def
  aspis_statement.pool_v1.pair_forest_trace.build_pool_v1_pair_forest_copy_registry_v1_loop.body
  (legacy : alloc.vec.Vec
  aspis_statement.pool_v1.pair_trace.PoolV1PairCopyLinkV1)
  (iter : alloc.vec.into_iter.IntoIter
  aspis_statement.pool_v1.pair_tree_hiding.PoolV1PairCopyRowLinkV1)
  (output : alloc.vec.Vec
  aspis_statement.pool_v1.pair_trace.PoolV1PairCopyLinkV1) :
  Result (ControlFlow ((alloc.vec.into_iter.IntoIter
    aspis_statement.pool_v1.pair_tree_hiding.PoolV1PairCopyRowLinkV1) ×
    (alloc.vec.Vec aspis_statement.pool_v1.pair_trace.PoolV1PairCopyLinkV1))
    ((core.result.Result (alloc.vec.Vec
    aspis_statement.pool_v1.pair_trace.PoolV1PairCopyLinkV1)
    aspis_statement.pool_v1.pair_trace.PoolV1PairTraceErrorV1) × Bool))
  := do
  let (o, iter1) ← alloc.vec.into_iter.IteratorIntoIter.next iter
  match o with
  | none =>
    let i := alloc.vec.Vec.len output
    if i !=
      aspis_statement.pool_v1.pair_forest_hiding.POOL_V1_PAIR_FOREST_COPY_ROW_LINKS_V1
    then
      ok (done (core.result.Result.Err
        aspis_statement.pool_v1.pair_trace.PoolV1PairTraceErrorV1.CopyLayout,
        false))
    else ok (done (core.result.Result.Ok output, true))
  | some scheduled =>
    let b ←
      aspis_statement.pool_v1.pair_forest_trace.path_kind scheduled.kind
    if b
    then
      match scheduled.kind with
      |
        aspis_statement.pool_v1.pair_tree_hiding.PoolV1PairCopyRowLinkKindV1.SpongeCarry
        _ _ =>
        ok (done (core.result.Result.Err
          aspis_statement.pool_v1.pair_trace.PoolV1PairTraceErrorV1.CopyLayout,
          false))
      |
        aspis_statement.pool_v1.pair_tree_hiding.PoolV1PairCopyRowLinkKindV1.OwnerOutput
        =>
        ok (done (core.result.Result.Err
          aspis_statement.pool_v1.pair_trace.PoolV1PairTraceErrorV1.CopyLayout,
          false))
      |
        aspis_statement.pool_v1.pair_tree_hiding.PoolV1PairCopyRowLinkKindV1.NullifierKey
        =>
        ok (done (core.result.Result.Err
          aspis_statement.pool_v1.pair_trace.PoolV1PairTraceErrorV1.CopyLayout,
          false))
      |
        aspis_statement.pool_v1.pair_tree_hiding.PoolV1PairCopyRowLinkKindV1.InputSaltHead
        =>
        ok (done (core.result.Result.Err
          aspis_statement.pool_v1.pair_trace.PoolV1PairTraceErrorV1.CopyLayout,
          false))
      |
        aspis_statement.pool_v1.pair_tree_hiding.PoolV1PairCopyRowLinkKindV1.InputSaltTail
        =>
        ok (done (core.result.Result.Err
          aspis_statement.pool_v1.pair_trace.PoolV1PairTraceErrorV1.CopyLayout,
          false))
      |
        aspis_statement.pool_v1.pair_tree_hiding.PoolV1PairCopyRowLinkKindV1.PrivatePathCurrent
        _ =>
        let i ←
          lift (core.convert.num.FromUsizeU16.from scheduled.producer_row)
        let producer ←
          aspis_statement.pool_v1.pair_forest_trace.tuple_cells i 0#usize
            8#usize false
        let i1 ←
          lift (core.convert.num.FromUsizeU16.from scheduled.consumer_row)
        let consumer ←
          aspis_statement.pool_v1.pair_forest_trace.tuple_cells i1 1#usize
            8#usize false
        if producer.row != scheduled.producer_row
        then
          ok (done (core.result.Result.Err
            aspis_statement.pool_v1.pair_trace.PoolV1PairTraceErrorV1.CopyLayout,
            false))
        else
          if consumer.row != scheduled.consumer_row
          then
            ok (done (core.result.Result.Err
              aspis_statement.pool_v1.pair_trace.PoolV1PairTraceErrorV1.CopyLayout,
              false))
          else
            let i2 := alloc.vec.Vec.len output
            let id ← lift (UScalar.cast .U16 i2)
            let i3 ← lift (core.convert.num.FromU32U16.from id)
            let i4 ←
              lift (Std.U32.wrapping_add
                aspis_statement.pool_v1.pair_trace.POOL_V1_PAIR_COPY_TAG_BASE_V1
                i3)
            let output1 ←
              alloc.vec.Vec.push output
                ({
                   id,
                   tag := i4,
                   kind := scheduled.kind,
                   weight :=
                     aspis_statement.pool_v1.pair_trace.PoolV1PairCopyWeightV1.One,
                   producer,
                   consumer
                 } : aspis_statement.pool_v1.pair_trace.PoolV1PairCopyLinkV1)
            ok (cont (iter1, output1))
      |
        aspis_statement.pool_v1.pair_tree_hiding.PoolV1PairCopyRowLinkKindV1.PrivatePathLeft
        _ =>
        let i ←
          lift (core.convert.num.FromUsizeU16.from scheduled.producer_row)
        let producer ←
          aspis_statement.pool_v1.pair_forest_trace.tuple_cells i 0#usize
            8#usize false
        let i1 ←
          lift (core.convert.num.FromUsizeU16.from scheduled.consumer_row)
        let consumer ←
          aspis_statement.pool_v1.pair_forest_trace.tuple_cells i1 0#usize
            8#usize false
        if producer.row != scheduled.producer_row
        then
          ok (done (core.result.Result.Err
            aspis_statement.pool_v1.pair_trace.PoolV1PairTraceErrorV1.CopyLayout,
            false))
        else
          if consumer.row != scheduled.consumer_row
          then
            ok (done (core.result.Result.Err
              aspis_statement.pool_v1.pair_trace.PoolV1PairTraceErrorV1.CopyLayout,
              false))
          else
            let i2 := alloc.vec.Vec.len output
            let id ← lift (UScalar.cast .U16 i2)
            let i3 ← lift (core.convert.num.FromU32U16.from id)
            let i4 ←
              lift (Std.U32.wrapping_add
                aspis_statement.pool_v1.pair_trace.POOL_V1_PAIR_COPY_TAG_BASE_V1
                i3)
            let output1 ←
              alloc.vec.Vec.push output
                ({
                   id,
                   tag := i4,
                   kind := scheduled.kind,
                   weight :=
                     aspis_statement.pool_v1.pair_trace.PoolV1PairCopyWeightV1.One,
                   producer,
                   consumer
                 } : aspis_statement.pool_v1.pair_trace.PoolV1PairCopyLinkV1)
            ok (cont (iter1, output1))
      |
        aspis_statement.pool_v1.pair_tree_hiding.PoolV1PairCopyRowLinkKindV1.PrivatePathRight
        _ =>
        let i ←
          lift (core.convert.num.FromUsizeU16.from scheduled.producer_row)
        let producer ←
          aspis_statement.pool_v1.pair_forest_trace.tuple_cells i 8#usize
            8#usize false
        let i1 ←
          lift (core.convert.num.FromUsizeU16.from scheduled.consumer_row)
        let consumer ←
          aspis_statement.pool_v1.pair_forest_trace.tuple_cells i1 8#usize
            8#usize true
        if producer.row != scheduled.producer_row
        then
          ok (done (core.result.Result.Err
            aspis_statement.pool_v1.pair_trace.PoolV1PairTraceErrorV1.CopyLayout,
            false))
        else
          if consumer.row != scheduled.consumer_row
          then
            ok (done (core.result.Result.Err
              aspis_statement.pool_v1.pair_trace.PoolV1PairTraceErrorV1.CopyLayout,
              false))
          else
            let i2 := alloc.vec.Vec.len output
            let id ← lift (UScalar.cast .U16 i2)
            let i3 ← lift (core.convert.num.FromU32U16.from id)
            let i4 ←
              lift (Std.U32.wrapping_add
                aspis_statement.pool_v1.pair_trace.POOL_V1_PAIR_COPY_TAG_BASE_V1
                i3)
            let output1 ←
              alloc.vec.Vec.push output
                ({
                   id,
                   tag := i4,
                   kind := scheduled.kind,
                   weight :=
                     aspis_statement.pool_v1.pair_trace.PoolV1PairCopyWeightV1.One,
                   producer,
                   consumer
                 } : aspis_statement.pool_v1.pair_trace.PoolV1PairCopyLinkV1)
            ok (cont (iter1, output1))
      |
        aspis_statement.pool_v1.pair_tree_hiding.PoolV1PairCopyRowLinkKindV1.ValueSource
        _ =>
        ok (done (core.result.Result.Err
          aspis_statement.pool_v1.pair_trace.PoolV1PairTraceErrorV1.CopyLayout,
          false))
      |
        aspis_statement.pool_v1.pair_tree_hiding.PoolV1PairCopyRowLinkKindV1.ConservationInput
        =>
        ok (done (core.result.Result.Err
          aspis_statement.pool_v1.pair_trace.PoolV1PairTraceErrorV1.CopyLayout,
          false))
      |
        aspis_statement.pool_v1.pair_tree_hiding.PoolV1PairCopyRowLinkKindV1.ConservationRecipient
        =>
        ok (done (core.result.Result.Err
          aspis_statement.pool_v1.pair_trace.PoolV1PairTraceErrorV1.CopyLayout,
          false))
      |
        aspis_statement.pool_v1.pair_tree_hiding.PoolV1PairCopyRowLinkKindV1.ConservationChange
        =>
        ok (done (core.result.Result.Err
          aspis_statement.pool_v1.pair_trace.PoolV1PairTraceErrorV1.CopyLayout,
          false))
      |
        aspis_statement.pool_v1.pair_tree_hiding.PoolV1PairCopyRowLinkKindV1.ConservationPartial
        =>
        ok (done (core.result.Result.Err
          aspis_statement.pool_v1.pair_trace.PoolV1PairTraceErrorV1.CopyLayout,
          false))
      |
        aspis_statement.pool_v1.pair_tree_hiding.PoolV1PairCopyRowLinkKindV1.InputSecondCommitment
        =>
        ok (done (core.result.Result.Err
          aspis_statement.pool_v1.pair_trace.PoolV1PairTraceErrorV1.CopyLayout,
          false))
      |
        aspis_statement.pool_v1.pair_tree_hiding.PoolV1PairCopyRowLinkKindV1.InputSelectedSide
        =>
        ok (done (core.result.Result.Err
          aspis_statement.pool_v1.pair_trace.PoolV1PairTraceErrorV1.CopyLayout,
          false))
      |
        aspis_statement.pool_v1.pair_tree_hiding.PoolV1PairCopyRowLinkKindV1.OutputSecondCommitment
        =>
        ok (done (core.result.Result.Err
          aspis_statement.pool_v1.pair_trace.PoolV1PairTraceErrorV1.CopyLayout,
          false))
      |
        aspis_statement.pool_v1.pair_tree_hiding.PoolV1PairCopyRowLinkKindV1.OutputPairFirst
        =>
        ok (done (core.result.Result.Err
          aspis_statement.pool_v1.pair_trace.PoolV1PairTraceErrorV1.CopyLayout,
          false))
      |
        aspis_statement.pool_v1.pair_tree_hiding.PoolV1PairCopyRowLinkKindV1.OutputPairFirstWithdrawal
        =>
        ok (done (core.result.Result.Err
          aspis_statement.pool_v1.pair_trace.PoolV1PairTraceErrorV1.CopyLayout,
          false))
      |
        aspis_statement.pool_v1.pair_tree_hiding.PoolV1PairCopyRowLinkKindV1.OutputPairSecond
        =>
        ok (done (core.result.Result.Err
          aspis_statement.pool_v1.pair_trace.PoolV1PairTraceErrorV1.CopyLayout,
          false))
      |
        aspis_statement.pool_v1.pair_tree_hiding.PoolV1PairCopyRowLinkKindV1.AppendCurrentLeft
        _ =>
        ok (done (core.result.Result.Err
          aspis_statement.pool_v1.pair_trace.PoolV1PairTraceErrorV1.CopyLayout,
          false))
      |
        aspis_statement.pool_v1.pair_tree_hiding.PoolV1PairCopyRowLinkKindV1.AppendCurrentRight
        _ =>
        ok (done (core.result.Result.Err
          aspis_statement.pool_v1.pair_trace.PoolV1PairTraceErrorV1.CopyLayout,
          false))
    else
      let s := alloc.vec.Vec.deref legacy
      let o1 ←
        aspis_statement.pool_v1.pair_forest_trace.first_link_of_kind s
          scheduled.kind
      let r ←
        core.option.Option.ok_or o1
          aspis_statement.pool_v1.pair_trace.PoolV1PairTraceErrorV1.CopyLayout
      let cf ← core.result.Result.Insts.CoreOpsTry.branch r
      match cf with
      | core.ops.control_flow.ControlFlow.Continue val =>
        let old ←
          alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
            aspis_statement.pool_v1.pair_trace.PoolV1PairCopyLinkV1) legacy val
        let producer ←
          aspis_statement.pool_v1.pair_forest_trace.translate_aux_tuple
            old.producer
        let consumer ←
          aspis_statement.pool_v1.pair_forest_trace.translate_aux_tuple
            old.consumer
        if producer.row != scheduled.producer_row
        then
          ok (done (core.result.Result.Err
            aspis_statement.pool_v1.pair_trace.PoolV1PairTraceErrorV1.CopyLayout,
            false))
        else
          if consumer.row != scheduled.consumer_row
          then
            ok (done (core.result.Result.Err
              aspis_statement.pool_v1.pair_trace.PoolV1PairTraceErrorV1.CopyLayout,
              false))
          else
            let i := alloc.vec.Vec.len output
            let id ← lift (UScalar.cast .U16 i)
            let i1 ← lift (core.convert.num.FromU32U16.from id)
            let i2 ←
              lift (Std.U32.wrapping_add
                aspis_statement.pool_v1.pair_trace.POOL_V1_PAIR_COPY_TAG_BASE_V1
                i1)
            let output1 ←
              alloc.vec.Vec.push output
                {
                  old
                    with
                    id, tag := i2, kind := scheduled.kind, producer, consumer
                }
            ok (cont (iter1, output1))
      | core.ops.control_flow.ControlFlow.Break residual =>
        let r1 ←
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
            (alloc.vec.Vec
            aspis_statement.pool_v1.pair_trace.PoolV1PairCopyLinkV1)
            (core.convert.FromSame
            aspis_statement.pool_v1.pair_trace.PoolV1PairTraceErrorV1) residual
        ok (done (r1, false))

-- block emitted by tool k2 (7271db7e), sha256 08625827ad02edb6a89c36e6d338c849bf63de59a3621d74af216123182d6ce8, source ['/home/dombarker/project-offloads/codex-pv-aspis-rewrite-20261111/src-rw/crates/aspis-statement/src/pool_v1/pair_forest_trace.rs', 568, 617]
def
  aspis_statement.pool_v1.pair_forest_trace.build_pool_v1_pair_forest_copy_registry_v1_loop
  (iter : alloc.vec.into_iter.IntoIter
  aspis_statement.pool_v1.pair_tree_hiding.PoolV1PairCopyRowLinkV1)
  (legacy : alloc.vec.Vec
  aspis_statement.pool_v1.pair_trace.PoolV1PairCopyLinkV1)
  (output : alloc.vec.Vec
  aspis_statement.pool_v1.pair_trace.PoolV1PairCopyLinkV1) :
  Result ((core.result.Result (alloc.vec.Vec
    aspis_statement.pool_v1.pair_trace.PoolV1PairCopyLinkV1)
    aspis_statement.pool_v1.pair_trace.PoolV1PairTraceErrorV1) × Bool)
  := do
  loop
    (fun (iter1, output1) =>
      aspis_statement.pool_v1.pair_forest_trace.build_pool_v1_pair_forest_copy_registry_v1_loop.body
      legacy iter1 output1)
    (iter, output)

-- block emitted by tool k2 (7271db7e), sha256 892d9afe4b34709fd8157e88174f8f780f247e2234895c729fd2befec7b79a12, source ['/home/dombarker/project-offloads/codex-pv-aspis-rewrite-20261111/src-rw/crates/aspis-statement/src/pool_v1/pair_forest_trace.rs', 562, 563]
def
  aspis_statement.pool_v1.pair_forest_trace.build_pool_v1_pair_forest_copy_registry_v1
  :
  Result (core.result.Result (alloc.vec.Vec
    aspis_statement.pool_v1.pair_trace.PoolV1PairCopyLinkV1)
    aspis_statement.pool_v1.pair_trace.PoolV1PairTraceErrorV1)
  := do
  let r ←
    aspis_statement.pool_v1.pair_trace.build_pool_v1_pair_copy_registry_v1
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let r1 ←
      aspis_statement.pool_v1.pair_forest_hiding.build_pool_v1_pair_forest_copy_row_schedule_v1
    let r2 ←
      core.result.Result.map_err
        aspis_statement.pool_v1.pair_forest_trace.build_pool_v1_pair_forest_copy_registry_v1.closure.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairHidingLayoutErrorV1PoolV1PairTraceErrorV1
        r1 ()
    let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r2
    match cf1 with
    | core.ops.control_flow.ControlFlow.Continue val1 =>
      let i := alloc.vec.Vec.len val1
      let output :=
        alloc.vec.Vec.with_capacity
          aspis_statement.pool_v1.pair_trace.PoolV1PairCopyLinkV1 i
      let iter ← alloc.vec.IntoIteratorVec.into_iter val1
      let (r3, loop_return) ←
        aspis_statement.pool_v1.pair_forest_trace.build_pool_v1_pair_forest_copy_registry_v1_loop
          iter val output
      if loop_return
      then ok r3
      else ok r3
    | core.ops.control_flow.ControlFlow.Break residual =>
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        (alloc.vec.Vec aspis_statement.pool_v1.pair_trace.PoolV1PairCopyLinkV1)
        (core.convert.FromSame
        aspis_statement.pool_v1.pair_trace.PoolV1PairTraceErrorV1) residual
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      (alloc.vec.Vec aspis_statement.pool_v1.pair_trace.PoolV1PairCopyLinkV1)
      (core.convert.FromSame
      aspis_statement.pool_v1.pair_trace.PoolV1PairTraceErrorV1) residual

end
end RW
end ProverPin2

#check @ProverPin2.RW.aspis_statement.pool_v1.pair_forest_trace.first_link_of_kind
#print axioms ProverPin2.RW.aspis_statement.pool_v1.pair_forest_trace.first_link_of_kind
example : type_of% @ProverPin2.RW.aspis_statement.pool_v1.pair_forest_trace.build_pool_v1_pair_forest_copy_registry_v1 = type_of% @ProverPin2.aspis_statement.pool_v1.pair_forest_trace.build_pool_v1_pair_forest_copy_registry_v1 := rfl
#check @ProverPin2.RW.aspis_statement.pool_v1.pair_forest_trace.build_pool_v1_pair_forest_copy_registry_v1
#print axioms ProverPin2.RW.aspis_statement.pool_v1.pair_forest_trace.build_pool_v1_pair_forest_copy_registry_v1
example : type_of% @ProverPin2.RW.aspis_statement.pool_v1.pair_trace.build_pool_v1_pair_copy_registry_v1 = type_of% @ProverPin2.aspis_statement.pool_v1.pair_trace.build_pool_v1_pair_copy_registry_v1 := rfl
#check @ProverPin2.RW.aspis_statement.pool_v1.pair_trace.build_pool_v1_pair_copy_registry_v1
#print axioms ProverPin2.RW.aspis_statement.pool_v1.pair_trace.build_pool_v1_pair_copy_registry_v1
example : type_of% @ProverPin2.RW.aspis_statement.pool_v1.pair_tree_hiding.build_pool_v1_pair_copy_row_schedule_v1 = type_of% @ProverPin2.aspis_statement.pool_v1.pair_tree_hiding.build_pool_v1_pair_copy_row_schedule_v1 := rfl
#check @ProverPin2.RW.aspis_statement.pool_v1.pair_tree_hiding.build_pool_v1_pair_copy_row_schedule_v1
#print axioms ProverPin2.RW.aspis_statement.pool_v1.pair_tree_hiding.build_pool_v1_pair_copy_row_schedule_v1
example : type_of% @ProverPin2.RW.aspis_statement.pool_v1.pair_tree_hiding.endpoint_counts = type_of% @ProverPin2.aspis_statement.pool_v1.pair_tree_hiding.endpoint_counts := rfl
#check @ProverPin2.RW.aspis_statement.pool_v1.pair_tree_hiding.endpoint_counts
#print axioms ProverPin2.RW.aspis_statement.pool_v1.pair_tree_hiding.endpoint_counts
-- 11 carried blocks, 0 new opaque items, 4 signature checks
