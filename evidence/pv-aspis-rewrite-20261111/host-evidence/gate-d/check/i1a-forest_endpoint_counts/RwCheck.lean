import ProverPin2.Funs
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048

namespace ProverPin2
namespace RW
noncomputable section

-- opaque item of the emission that package g2 does not declare, block sha256 aa5f25b668dc3ffd55db885f331888ee1c333e60dd4ec20712725e5c9da9404e
axiom alloc.vec.Vec.reserve
  {T : Type} (A : Type) :
  alloc.vec.Vec T → Std.Usize → Result (alloc.vec.Vec T)

-- opaque item of the emission that package g2 does not declare, block sha256 68f6f258f662473f945d0f7d0bf9e73b2fe71874d2f9c42365ef713a15b0e68e
axiom
  core.iter.adapters.filter.Filter.Insts.CoreIterTraitsIteratorIterator.next
  {I : Type} {P : Type} {Clause0_Item : Type} (traitsiteratorIteratorInst :
  core.iter.traits.iterator.Iterator I Clause0_Item)
  (opsfunctionFnMutPTupleShared0Clause0_ItemBoolInst : core.ops.function.FnMut
  P Clause0_Item Bool) :
  core.iter.adapters.filter.Filter I P → Result ((Option Clause0_Item) ×
    (core.iter.adapters.filter.Filter I P))

-- block emitted by tool k2 (7271db7e), sha256 7a30e635ca6e2141e8d8b557aa6e5a83f2b63e0687bb7175758760da40777ea9, source ['/rustc/library/core/src/iter/adapters/filter.rs', 90, 92]
impl_def core.iter.adapters.filter.Filter.Insts.CoreIterTraitsIteratorIterator
  {I : Type} {P : Type} {Clause0_Item : Type} (traitsiteratorIteratorInst :
  core.iter.traits.iterator.Iterator I Clause0_Item)
  (opsfunctionFnMutPTupleSharedClause0_ItemBoolInst : core.ops.function.FnMut P
  Clause0_Item Bool) : core.iter.traits.iterator.Iterator
  (core.iter.adapters.filter.Filter I P) Clause0_Item := {
  next :=
    core.iter.adapters.filter.Filter.Insts.CoreIterTraitsIteratorIterator.next
    traitsiteratorIteratorInst opsfunctionFnMutPTupleSharedClause0_ItemBoolInst
  filter := fun {P1 : Type} (opsfunctionFnMutPTupleSharedPBoolInst :
    core.ops.function.FnMut P1 Clause0_Item Bool) =>
    core.iter.traits.iterator.Iterator.filter.default
    (core.iter.adapters.filter.Filter.Insts.CoreIterTraitsIteratorIterator
    traitsiteratorIteratorInst
    opsfunctionFnMutPTupleSharedClause0_ItemBoolInst)
    opsfunctionFnMutPTupleSharedPBoolInst
  collect := fun {B : Type} (collectFromIteratorInst :
    core.iter.traits.collect.FromIterator B Clause0_Item) =>
    core.iter.traits.iterator.Iterator.collect.default
    (core.iter.adapters.filter.Filter.Insts.CoreIterTraitsIteratorIterator
    traitsiteratorIteratorInst
    opsfunctionFnMutPTupleSharedClause0_ItemBoolInst) collectFromIteratorInst
}

-- block emitted by tool k2 (7271db7e), sha256 718245e7a82785cc09e84c99a2e1baf9ba1360463ace7ce6c033ba284f2fe858, source ['/home/dombarker/project-offloads/codex-pv-aspis-rewrite-20261111/src-rw/crates/aspis-statement/src/pool_v1/pair_forest_hiding.rs', 110, 123]
def aspis_statement.pool_v1.pair_forest_hiding.endpoint_counts_loop.body
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

-- block emitted by tool k2 (7271db7e), sha256 79385b298fac3f46e8f33923ed2624bf5d0b7222337c142a26319f60e23cdc56, source ['/home/dombarker/project-offloads/codex-pv-aspis-rewrite-20261111/src-rw/crates/aspis-statement/src/pool_v1/pair_forest_hiding.rs', 110, 123]
def aspis_statement.pool_v1.pair_forest_hiding.endpoint_counts_loop
  (iter : core.slice.iter.Iter
  aspis_statement.pool_v1.pair_tree_hiding.PoolV1PairCopyRowLinkV1)
  (producers : Array Std.U8 1024#usize) (consumers : Array Std.U8 1024#usize) :
  Result (core.result.Result ((Array Std.U8 1024#usize) × (Array Std.U8
    1024#usize))
    aspis_statement.pool_v1.pair_tree_hiding.PoolV1PairHidingLayoutErrorV1)
  := do
  loop
    (fun (iter1, producers1, consumers1) =>
      aspis_statement.pool_v1.pair_forest_hiding.endpoint_counts_loop.body
      iter1 producers1 consumers1)
    (iter, producers, consumers)

-- block emitted by tool k2 (7271db7e), sha256 8fa820bd431e0c5a39952f3fa1f712b976a868e5ff5df3d91f3b92dbb4ce595d, source ['/home/dombarker/project-offloads/codex-pv-aspis-rewrite-20261111/src-rw/crates/aspis-statement/src/pool_v1/pair_forest_hiding.rs', 101, 103]
def aspis_statement.pool_v1.pair_forest_hiding.endpoint_counts
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
  aspis_statement.pool_v1.pair_forest_hiding.endpoint_counts_loop iter
    producers consumers

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

-- block emitted by tool k2 (7271db7e), sha256 8a96b011d2c2e2ea66fd6877d7780dd0fc06bbd8f9f86779faf8bf308ceee959, source ['/home/dombarker/project-offloads/codex-pv-aspis-rewrite-20261111/src-rw/crates/aspis-statement/src/pool_v1/pair_forest_hiding.rs', 172, 204]
def
  aspis_statement.pool_v1.pair_forest_hiding.build_pool_v1_pair_forest_copy_row_schedule_v1_loop0_loop0.body
  (iter : core.ops.range.Range Std.Usize)
  (links : alloc.vec.Vec
  aspis_statement.pool_v1.pair_tree_hiding.PoolV1PairCopyRowLinkV1) :
  Result (ControlFlow ((core.ops.range.Range Std.Usize) × (alloc.vec.Vec
    aspis_statement.pool_v1.pair_tree_hiding.PoolV1PairCopyRowLinkV1))
    ((core.result.Result (alloc.vec.Vec
    aspis_statement.pool_v1.pair_tree_hiding.PoolV1PairCopyRowLinkV1)
    aspis_statement.pool_v1.pair_tree_hiding.PoolV1PairHidingLayoutErrorV1) ×
    Bool))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none =>
    let i := alloc.vec.Vec.len links
    if i !=
      aspis_statement.pool_v1.pair_forest_hiding.POOL_V1_PAIR_FOREST_COPY_ROW_LINKS_V1
    then
      ok (done (core.result.Result.Err
        aspis_statement.pool_v1.pair_tree_hiding.PoolV1PairHidingLayoutErrorV1.Shape,
        false))
    else
      let s := alloc.vec.Vec.deref links
      let r ← aspis_statement.pool_v1.pair_forest_hiding.endpoint_counts s
      let cf ← core.result.Result.Insts.CoreOpsTry.branch r
      match cf with
      | core.ops.control_flow.ControlFlow.Continue _ =>
        ok (done (core.result.Result.Ok links, true))
      | core.ops.control_flow.ControlFlow.Break residual =>
        let r1 ←
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
            (alloc.vec.Vec
            aspis_statement.pool_v1.pair_tree_hiding.PoolV1PairCopyRowLinkV1)
            (core.convert.FromSame
            aspis_statement.pool_v1.pair_tree_hiding.PoolV1PairHidingLayoutErrorV1)
            residual
        ok (done (r1, false))
  | some level =>
    let o1 ←
      aspis_statement.pool_v1.pair_forest_hiding.pool_v1_pair_forest_path_base_row_v1
        level
    let r ←
      core.option.Option.ok_or o1
        aspis_statement.pool_v1.pair_tree_hiding.PoolV1PairHidingLayoutErrorV1.Shape
    let cf ← core.result.Result.Insts.CoreOpsTry.branch r
    match cf with
    | core.ops.control_flow.ControlFlow.Continue val =>
      let o2 ←
        aspis_statement.pool_v1.pair_forest_hiding.pool_v1_pair_forest_membership_hash_block_v1
          level
      let r1 ←
        core.option.Option.ok_or o2
          aspis_statement.pool_v1.pair_tree_hiding.PoolV1PairHidingLayoutErrorV1.Shape
      let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
      match cf1 with
      | core.ops.control_flow.ControlFlow.Continue val1 =>
        if level = 0#usize
        then
          let i ← lift (UScalar.cast .U8 level)
          let i1 ←
            lift (Std.Usize.wrapping_mul 3#usize
              aspis_statement.pool_v1.pair_tree_profile.POOL_V1_PAIR_TRACE_BLOCK_ROWS)
          let i2 ← lift (Std.Usize.wrapping_add i1 11#usize)
          let pvpcrlv ←
            aspis_statement.pool_v1.pair_forest_hiding.link
              (aspis_statement.pool_v1.pair_tree_hiding.PoolV1PairCopyRowLinkKindV1.PrivatePathCurrent
              i) i2 val
          let links1 ← alloc.vec.Vec.push links pvpcrlv
          let i3 ← lift (UScalar.cast .U8 level)
          let i4 ← lift (Std.Usize.wrapping_add val 1#usize)
          let i5 ←
            lift (Std.Usize.wrapping_mul val1
              aspis_statement.pool_v1.pair_tree_profile.POOL_V1_PAIR_TRACE_BLOCK_ROWS)
          let i6 ← lift (Std.Usize.wrapping_add i5 12#usize)
          let pvpcrlv1 ←
            aspis_statement.pool_v1.pair_forest_hiding.link
              (aspis_statement.pool_v1.pair_tree_hiding.PoolV1PairCopyRowLinkKindV1.PrivatePathLeft
              i3) i4 i6
          let links2 ← alloc.vec.Vec.push links1 pvpcrlv1
          let i7 ← lift (UScalar.cast .U8 level)
          let i8 ← lift (Std.Usize.wrapping_add val 1#usize)
          let i9 ←
            lift (Std.Usize.wrapping_mul val1
              aspis_statement.pool_v1.pair_tree_profile.POOL_V1_PAIR_TRACE_BLOCK_ROWS)
          let pvpcrlv2 ←
            aspis_statement.pool_v1.pair_forest_hiding.link
              (aspis_statement.pool_v1.pair_tree_hiding.PoolV1PairCopyRowLinkKindV1.PrivatePathRight
              i7) i8 i9
          let links3 ← alloc.vec.Vec.push links2 pvpcrlv2
          ok (cont (iter1, links3))
        else
          let i ← lift (Std.Usize.wrapping_sub level 1#usize)
          let o3 ←
            aspis_statement.pool_v1.pair_forest_hiding.pool_v1_pair_forest_membership_hash_block_v1
              i
          let r2 ←
            core.option.Option.ok_or o3
              aspis_statement.pool_v1.pair_tree_hiding.PoolV1PairHidingLayoutErrorV1.Shape
          let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r2
          match cf2 with
          | core.ops.control_flow.ControlFlow.Continue val2 =>
            let i1 ← lift (UScalar.cast .U8 level)
            let i2 ←
              lift (Std.Usize.wrapping_mul val2
                aspis_statement.pool_v1.pair_tree_profile.POOL_V1_PAIR_TRACE_BLOCK_ROWS)
            let i3 ← lift (Std.Usize.wrapping_add i2 11#usize)
            let pvpcrlv ←
              aspis_statement.pool_v1.pair_forest_hiding.link
                (aspis_statement.pool_v1.pair_tree_hiding.PoolV1PairCopyRowLinkKindV1.PrivatePathCurrent
                i1) i3 val
            let links1 ← alloc.vec.Vec.push links pvpcrlv
            let i4 ← lift (UScalar.cast .U8 level)
            let i5 ← lift (Std.Usize.wrapping_add val 1#usize)
            let i6 ←
              lift (Std.Usize.wrapping_mul val1
                aspis_statement.pool_v1.pair_tree_profile.POOL_V1_PAIR_TRACE_BLOCK_ROWS)
            let i7 ← lift (Std.Usize.wrapping_add i6 12#usize)
            let pvpcrlv1 ←
              aspis_statement.pool_v1.pair_forest_hiding.link
                (aspis_statement.pool_v1.pair_tree_hiding.PoolV1PairCopyRowLinkKindV1.PrivatePathLeft
                i4) i5 i7
            let links2 ← alloc.vec.Vec.push links1 pvpcrlv1
            let i8 ← lift (UScalar.cast .U8 level)
            let i9 ← lift (Std.Usize.wrapping_add val 1#usize)
            let i10 ←
              lift (Std.Usize.wrapping_mul val1
                aspis_statement.pool_v1.pair_tree_profile.POOL_V1_PAIR_TRACE_BLOCK_ROWS)
            let pvpcrlv2 ←
              aspis_statement.pool_v1.pair_forest_hiding.link
                (aspis_statement.pool_v1.pair_tree_hiding.PoolV1PairCopyRowLinkKindV1.PrivatePathRight
                i8) i9 i10
            let links3 ← alloc.vec.Vec.push links2 pvpcrlv2
            ok (cont (iter1, links3))
          | core.ops.control_flow.ControlFlow.Break residual =>
            let r3 ←
              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                (alloc.vec.Vec
                aspis_statement.pool_v1.pair_tree_hiding.PoolV1PairCopyRowLinkV1)
                (core.convert.FromSame
                aspis_statement.pool_v1.pair_tree_hiding.PoolV1PairHidingLayoutErrorV1)
                residual
            ok (done (r3, false))
      | core.ops.control_flow.ControlFlow.Break residual =>
        let r2 ←
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
            (alloc.vec.Vec
            aspis_statement.pool_v1.pair_tree_hiding.PoolV1PairCopyRowLinkV1)
            (core.convert.FromSame
            aspis_statement.pool_v1.pair_tree_hiding.PoolV1PairHidingLayoutErrorV1)
            residual
        ok (done (r2, false))
    | core.ops.control_flow.ControlFlow.Break residual =>
      let r1 ←
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          (alloc.vec.Vec
          aspis_statement.pool_v1.pair_tree_hiding.PoolV1PairCopyRowLinkV1)
          (core.convert.FromSame
          aspis_statement.pool_v1.pair_tree_hiding.PoolV1PairHidingLayoutErrorV1)
          residual
      ok (done (r1, false))

-- block emitted by tool k2 (7271db7e), sha256 db2be1e2b160414546eb3f7a9e8d86bf64028d7687d3dccc20b5f0ac75466c9e, source ['/home/dombarker/project-offloads/codex-pv-aspis-rewrite-20261111/src-rw/crates/aspis-statement/src/pool_v1/pair_forest_hiding.rs', 172, 204]
def
  aspis_statement.pool_v1.pair_forest_hiding.build_pool_v1_pair_forest_copy_row_schedule_v1_loop0_loop0
  (iter : core.ops.range.Range Std.Usize)
  (links : alloc.vec.Vec
  aspis_statement.pool_v1.pair_tree_hiding.PoolV1PairCopyRowLinkV1) :
  Result ((core.result.Result (alloc.vec.Vec
    aspis_statement.pool_v1.pair_tree_hiding.PoolV1PairCopyRowLinkV1)
    aspis_statement.pool_v1.pair_tree_hiding.PoolV1PairHidingLayoutErrorV1) ×
    Bool)
  := do
  loop
    (fun (iter1, links1) =>
      aspis_statement.pool_v1.pair_forest_hiding.build_pool_v1_pair_forest_copy_row_schedule_v1_loop0_loop0.body
      iter1 links1)
    (iter, links)

-- block emitted by tool k2 (7271db7e), sha256 5721f17793ecc3f66a8f426c0c84a376d56fc52158834a9026142d825740b375, source ['/home/dombarker/project-offloads/codex-pv-aspis-rewrite-20261111/src-rw/crates/aspis-statement/src/pool_v1/pair_forest_hiding.rs', 163, 204]
def
  aspis_statement.pool_v1.pair_forest_hiding.build_pool_v1_pair_forest_copy_row_schedule_v1_loop0.body
  (into_iter_back : core.slice.iter.IterMut
  aspis_statement.pool_v1.pair_tree_hiding.PoolV1PairCopyRowLinkV1 →
  alloc.vec.Vec
  aspis_statement.pool_v1.pair_tree_hiding.PoolV1PairCopyRowLinkV1)
  (iter : core.slice.iter.IterMut
  aspis_statement.pool_v1.pair_tree_hiding.PoolV1PairCopyRowLinkV1)
  (back : core.slice.iter.IterMut
  aspis_statement.pool_v1.pair_tree_hiding.PoolV1PairCopyRowLinkV1 →
  core.slice.iter.IterMut
  aspis_statement.pool_v1.pair_tree_hiding.PoolV1PairCopyRowLinkV1) :
  Result (ControlFlow ((core.slice.iter.IterMut
    aspis_statement.pool_v1.pair_tree_hiding.PoolV1PairCopyRowLinkV1) ×
    (core.slice.iter.IterMut
    aspis_statement.pool_v1.pair_tree_hiding.PoolV1PairCopyRowLinkV1 →
    core.slice.iter.IterMut
    aspis_statement.pool_v1.pair_tree_hiding.PoolV1PairCopyRowLinkV1))
    ((core.result.Result (alloc.vec.Vec
    aspis_statement.pool_v1.pair_tree_hiding.PoolV1PairCopyRowLinkV1)
    aspis_statement.pool_v1.pair_tree_hiding.PoolV1PairHidingLayoutErrorV1) ×
    Bool × Bool))
  := do
  let (o, iter1, next_back) ← core.slice.iter.IteratorIterMut.next iter
  match o with
  | none =>
    let iter2 := next_back iter1 none
    let links := into_iter_back (back iter2)
    let i ←
      lift (Std.Usize.wrapping_mul 3#usize
        aspis_statement.pool_v1.pair_forest_hiding.POOL_V1_PAIR_FOREST_PRIVATE_DIRECTIONS_V1)
    let links1 ← alloc.vec.Vec.reserve Global links i
    let (r, loop_return) ←
      aspis_statement.pool_v1.pair_forest_hiding.build_pool_v1_pair_forest_copy_row_schedule_v1_loop0_loop0
        {
          start := 0#usize,
          «end» :=
            aspis_statement.pool_v1.pair_forest_hiding.POOL_V1_PAIR_FOREST_PRIVATE_DIRECTIONS_V1
        } links1
    if loop_return
    then ok (done (r, true, false))
    else ok (done (r, false, true))
  | some scheduled =>
    let i ← lift (core.convert.num.FromUsizeU16.from scheduled.producer_row)
    let i1 ←
      lift (Std.Usize.wrapping_mul 54#usize
        aspis_statement.pool_v1.pair_tree_profile.POOL_V1_PAIR_TRACE_BLOCK_ROWS)
    let (i2, back1) ←
      if i >= i1
      then
        do
        let i3 ←
          lift (UScalar.cast .U16
            aspis_statement.pool_v1.pair_tree_profile.POOL_V1_PAIR_TRACE_BLOCK_ROWS)
        let i4 ← lift (Std.U16.wrapping_mul 3#u16 i3)
        let i5 ← lift (Std.U16.wrapping_add scheduled.producer_row i4)
        ok (i5, fun pvpcrlv im => next_back im (some pvpcrlv))
      else
        ok (scheduled.producer_row,
          fun pvpcrlv im => next_back im (some pvpcrlv))
    let i3 ← lift (core.convert.num.FromUsizeU16.from scheduled.consumer_row)
    let i4 ←
      lift (Std.Usize.wrapping_mul 54#usize
        aspis_statement.pool_v1.pair_tree_profile.POOL_V1_PAIR_TRACE_BLOCK_ROWS)
    if i3 >= i4
    then
      let i5 ←
        lift (UScalar.cast .U16
          aspis_statement.pool_v1.pair_tree_profile.POOL_V1_PAIR_TRACE_BLOCK_ROWS)
      let i6 ← lift (Std.U16.wrapping_mul 3#u16 i5)
      let i7 ← lift (Std.U16.wrapping_add scheduled.consumer_row i6)
      ok (cont (iter1,
        fun im =>
          let im1 :=
            back1 { scheduled with producer_row := i2, consumer_row := i7 } im
          back im1))
    else
      ok (cont (iter1,
        fun im =>
          let im1 := back1 { scheduled with producer_row := i2 } im
          back im1))

-- block emitted by tool k2 (7271db7e), sha256 40cd687248c6791910456a5261cd9f36ed09f75e604c8e448fe263fde41bd86a, source ['/home/dombarker/project-offloads/codex-pv-aspis-rewrite-20261111/src-rw/crates/aspis-statement/src/pool_v1/pair_forest_hiding.rs', 163, 204]
def
  aspis_statement.pool_v1.pair_forest_hiding.build_pool_v1_pair_forest_copy_row_schedule_v1_loop0
  (into_iter_back : core.slice.iter.IterMut
  aspis_statement.pool_v1.pair_tree_hiding.PoolV1PairCopyRowLinkV1 →
  alloc.vec.Vec
  aspis_statement.pool_v1.pair_tree_hiding.PoolV1PairCopyRowLinkV1)
  (iter : core.slice.iter.IterMut
  aspis_statement.pool_v1.pair_tree_hiding.PoolV1PairCopyRowLinkV1)
  (back : core.slice.iter.IterMut
  aspis_statement.pool_v1.pair_tree_hiding.PoolV1PairCopyRowLinkV1 →
  core.slice.iter.IterMut
  aspis_statement.pool_v1.pair_tree_hiding.PoolV1PairCopyRowLinkV1) :
  Result ((core.result.Result (alloc.vec.Vec
    aspis_statement.pool_v1.pair_tree_hiding.PoolV1PairCopyRowLinkV1)
    aspis_statement.pool_v1.pair_tree_hiding.PoolV1PairHidingLayoutErrorV1) ×
    Bool × Bool)
  := do
  loop
    (fun (iter1, back1) =>
      aspis_statement.pool_v1.pair_forest_hiding.build_pool_v1_pair_forest_copy_row_schedule_v1_loop0.body
      into_iter_back iter1 back1)
    (iter, back)

-- block emitted by tool k2 (7271db7e), sha256 2450cdd8346a4480dd9d7d912b0ba11e4c381663308e795466d90db751747fae, source ['/home/dombarker/project-offloads/codex-pv-aspis-rewrite-20261111/src-rw/crates/aspis-statement/src/pool_v1/pair_forest_hiding.rs', 147, 148]
def
  aspis_statement.pool_v1.pair_forest_hiding.build_pool_v1_pair_forest_copy_row_schedule_v1
  :
  Result (core.result.Result (alloc.vec.Vec
    aspis_statement.pool_v1.pair_tree_hiding.PoolV1PairCopyRowLinkV1)
    aspis_statement.pool_v1.pair_tree_hiding.PoolV1PairHidingLayoutErrorV1)
  := do
  let r ←
    aspis_statement.pool_v1.pair_tree_hiding.build_pool_v1_pair_copy_row_schedule_v1
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let ii ← alloc.vec.IntoIteratorVec.into_iter val
    let f ←
      core.iter.traits.iterator.Iterator.filter.default
        (core.iter.traits.iterator.IteratorVecIntoIter
        aspis_statement.pool_v1.pair_tree_hiding.PoolV1PairCopyRowLinkV1)
        aspis_statement.pool_v1.pair_forest_hiding.build_pool_v1_pair_forest_copy_row_schedule_v1.closure.Insts.CoreOpsFunctionFnMutTupleSharedPoolV1PairCopyRowLinkV1Bool
        ii ()
    let links ←
      core.iter.traits.iterator.Iterator.collect.default
        (core.iter.adapters.filter.Filter.Insts.CoreIterTraitsIteratorIterator
        (core.iter.traits.iterator.IteratorVecIntoIter
        aspis_statement.pool_v1.pair_tree_hiding.PoolV1PairCopyRowLinkV1)
        aspis_statement.pool_v1.pair_forest_hiding.build_pool_v1_pair_forest_copy_row_schedule_v1.closure.Insts.CoreOpsFunctionFnMutTupleSharedPoolV1PairCopyRowLinkV1Bool)
        (core.iter.traits.collect.FromIteratorVec
        aspis_statement.pool_v1.pair_tree_hiding.PoolV1PairCopyRowLinkV1) f
    let (iter, into_iter_back) ←
      MutAVec.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter
        Global links
    let (r1, loop_return, loop_return1) ←
      aspis_statement.pool_v1.pair_forest_hiding.build_pool_v1_pair_forest_copy_row_schedule_v1_loop0
        into_iter_back iter (fun im => im)
    massert (loop_return || loop_return1)
    if loop_return
    then ok r1
    else ok r1
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      (alloc.vec.Vec
      aspis_statement.pool_v1.pair_tree_hiding.PoolV1PairCopyRowLinkV1)
      (core.convert.FromSame
      aspis_statement.pool_v1.pair_tree_hiding.PoolV1PairHidingLayoutErrorV1)
      residual

end
end RW
end ProverPin2

#check @ProverPin2.RW.aspis_statement.pool_v1.pair_forest_hiding.endpoint_counts
#print axioms ProverPin2.RW.aspis_statement.pool_v1.pair_forest_hiding.endpoint_counts
example : type_of% @ProverPin2.RW.aspis_statement.pool_v1.pair_forest_hiding.build_pool_v1_pair_forest_copy_row_schedule_v1 = type_of% @aspis_statement.pool_v1.pair_forest_hiding.build_pool_v1_pair_forest_copy_row_schedule_v1 := rfl
#check @ProverPin2.RW.aspis_statement.pool_v1.pair_forest_hiding.build_pool_v1_pair_forest_copy_row_schedule_v1
#print axioms ProverPin2.RW.aspis_statement.pool_v1.pair_forest_hiding.build_pool_v1_pair_forest_copy_row_schedule_v1
example : type_of% @ProverPin2.RW.aspis_statement.pool_v1.pair_tree_hiding.endpoint_counts = type_of% @ProverPin2.aspis_statement.pool_v1.pair_tree_hiding.endpoint_counts := rfl
#check @ProverPin2.RW.aspis_statement.pool_v1.pair_tree_hiding.endpoint_counts
#print axioms ProverPin2.RW.aspis_statement.pool_v1.pair_tree_hiding.endpoint_counts
-- 12 carried blocks, 2 new opaque items, 2 signature checks
