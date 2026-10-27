import R1Z.PV_RunJoin_UniversalTreeFrame22
set_option autoImplicit false
namespace R1Z.PV_RunJoin_UniversalAppend22
open Aeneas Aeneas.Std Result
open BuilderForestAdmissionPort BuilderForestAdmissionPort.pool_v1 BuilderRecordsFields
open PV_RunJoin_UniversalTreeFrame22

/-- The nominal public-tree wrapper preserves the universal owned append
index/receipt law. This does not evaluate reconstruction or any root hash. -/
theorem append_next [ExternalLinear]
    (tree next : incremental_merkle.IncrementalMerkleTreeV1)
    (leaf : Digest) (roots : Roots) (receipt : incremental_merkle.AppendOneV1)
    (h : incremental_merkle.IncrementalMerkleTreeV1.append_one_with_empty_roots tree leaf roots =
      ok (.Ok (next,receipt))) :
    next.next_leaf_index = U64.wrapping_add tree.next_leaf_index 1#u64 ∧
      receipt.leaf_index = tree.next_leaf_index ∧
      receipt.root_sequence = next.next_leaf_index ∧ receipt.root = next.root := by
  unfold incremental_merkle.IncrementalMerkleTreeV1.append_one_with_empty_roots at h
  obtain ⟨constructed,hc,h⟩ := bind_ok_inv h
  cases constructed with
  | Err error =>
    change (ok (.Err error) : Result (core.result.Result _ _)) = ok (.Ok (next,receipt)) at h
    cases h
  | Ok owned =>
    have frame := construct tree.next_leaf_index tree.root tree.frontier roots owned hc
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at h
    obtain ⟨appended,ha,h⟩ := bind_ok_inv h
    cases appended with
    | Err error =>
      change (ok (.Err error) : Result (core.result.Result _ _)) = ok (.Ok (next,receipt)) at h
      cases h
    | Ok pair =>
      rcases pair with ⟨ownedNext,rec⟩
      have fields := append owned ownedNext leaf rec ha
      change (ok (.Ok (ownedNext.inner,rec)) : Result (core.result.Result
        (incremental_merkle.IncrementalMerkleTreeV1 × incremental_merkle.AppendOneV1)
        incremental_merkle.PoolV1TreeError)) = ok (.Ok (next,receipt)) at h
      have same := core.result.Result.Ok.inj (Result.ok.inj h)
      cases same
      rw [frame.1] at fields
      exact fields
#print axioms append_next

theorem late_sequence [ExternalLinear]
    (records : pair_forest_copy_builder.CopyRecords)
    (snapshot : pair_tree_profile.PoolV1PairLiveSnapshotV1) (leaf : Digest)
    (afterstate : pair_terminal.PoolV1PairVerifiedAfterstateV1)
    (h : pair_forest_trace.late_append records snapshot leaf = ok (.Ok afterstate)) :
    snapshot.sequence = snapshot.next_pair_index := by
  by_contra different
  rw [pair_forest_trace.late_append] at h
  simp [different] at h
#print axioms late_sequence
end R1Z.PV_RunJoin_UniversalAppend22
