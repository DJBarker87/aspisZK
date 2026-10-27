import R1Z.PV_RunJoin_UniversalAppend22
import R1Z.PV_RunJoin_UniversalReturnedLate22
set_option autoImplicit false
namespace R1Z.PV_RunJoin_UniversalAfterIndex22
open Aeneas Aeneas.Std Result
open BuilderForestAdmissionPort BuilderForestAdmissionPort.pool_v1 BuilderRecordsFields
open PV_RunJoin_UniversalTreeFrame22

theorem constructed [ExternalLinear] (index : U64) (root : Digest) (frontier : Frontier)
    (roots : Roots) (tree : incremental_merkle.IncrementalMerkleTreeV1)
    (h : incremental_merkle.IncrementalMerkleTreeV1.from_parts_with_empty_roots index root frontier roots =
      ok (.Ok tree)) : tree = ⟨index,root,frontier⟩ := by
  unfold incremental_merkle.IncrementalMerkleTreeV1.from_parts_with_empty_roots at h
  obtain ⟨result,hr,h⟩ := bind_ok_inv h
  cases result with
  | Err error => cases h
  | Ok owned =>
    have frame := construct index root frontier roots owned hr
    change ok (.Ok owned.inner) = ok (.Ok tree) at h
    exact (core.result.Result.Ok.inj (Result.ok.inj h)).symm.trans frame.1
#print axioms constructed

theorem next_of_parts [ExternalLinear] {index : U64} {root : Digest} {frontier : Frontier}
    {roots : Roots} {tree after : incremental_merkle.IncrementalMerkleTreeV1}
    {leaf : Digest} {receipt : incremental_merkle.AppendOneV1}
    (hc : incremental_merkle.IncrementalMerkleTreeV1.from_parts_with_empty_roots index root frontier roots =
      ok (.Ok tree))
    (ha : incremental_merkle.IncrementalMerkleTreeV1.append_one_with_empty_roots tree leaf roots =
      ok (.Ok (after,receipt))) :
    after.next_leaf_index = U64.wrapping_add index 1#u64 := by
  have hnext := (PV_RunJoin_UniversalAppend22.append_next tree after leaf roots receipt ha).1
  rw [constructed index root frontier roots tree hc] at hnext
  exact hnext
#print axioms next_of_parts

theorem late_next [ExternalLinear]
    (records : pair_forest_copy_builder.CopyRecords)
    (snapshot : pair_tree_profile.PoolV1PairLiveSnapshotV1) (leaf : Digest)
    (afterstate : pair_terminal.PoolV1PairVerifiedAfterstateV1)
    (h : pair_forest_trace.late_append records snapshot leaf = ok (.Ok afterstate)) :
    afterstate.next_pair_index = U64.wrapping_add snapshot.next_pair_index 1#u64 := by
  unfold pair_forest_trace.late_append at h
  repeat' first
    | (have _test : core.result.Result _ _ := value; cases value <;>
        simp only [BuilderForestStdPort.core.result.Result.map_err,BuilderAdmissionStd.mapErr,
          core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at h)
    | (pv_peel h with value hvalue)
    | exact False.elim (PV_Src_ResultControl.error_ne_ok _ _ h)
    | exact False.elim (PV_Src_ResultControl.same_residual_ne_ok _ _ h)
    | (have _test : Bool := value; cases value <;> simp only [Bool.false_eq_true, ↓reduceIte] at h)
    | (have _test : core.ops.control_flow.ControlFlow _ _ := value; cases value)
    | (have _test : _ × _ := value; rcases value with ⟨value,rest⟩)
    | (split at h)
    | (cases h)
  all_goals apply next_of_parts <;> assumption
#print axioms late_next
end R1Z.PV_RunJoin_UniversalAfterIndex22
