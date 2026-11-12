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

end
end RW
end ProverPin2

example : type_of% @ProverPin2.RW.aspis_statement.pool_v1.pair_tree_hiding.endpoint_counts = type_of% @ProverPin2.aspis_statement.pool_v1.pair_tree_hiding.endpoint_counts := rfl
#check @ProverPin2.RW.aspis_statement.pool_v1.pair_tree_hiding.endpoint_counts
#print axioms ProverPin2.RW.aspis_statement.pool_v1.pair_tree_hiding.endpoint_counts
-- 3 carried blocks, 0 new opaque items, 1 signature checks
