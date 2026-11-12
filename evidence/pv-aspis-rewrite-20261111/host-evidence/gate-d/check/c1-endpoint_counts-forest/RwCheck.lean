import ProverPin2.Funs
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048

namespace ProverPin2
namespace RW
noncomputable section

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

end
end RW
end ProverPin2

#check @ProverPin2.RW.aspis_statement.pool_v1.pair_forest_hiding.endpoint_counts
#print axioms ProverPin2.RW.aspis_statement.pool_v1.pair_forest_hiding.endpoint_counts
-- 3 carried blocks, 0 new opaque items, 0 signature checks
