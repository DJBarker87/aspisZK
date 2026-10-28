import R1Z.PV_RunJoin_RootConstructor31
set_option autoImplicit false
namespace R1Z.PV_RunJoin_AppendCapacity31
open Aeneas Aeneas.Std Result BuilderForestAdmissionPort BuilderForestAdmissionPort.pool_v1
open PV_RunJoin_UniversalTreeFrame22

theorem owned [ExternalLinear] (tree next : incremental_merkle.tree_reference.OwnedTree)
    (leaf : Digest) (receipt : incremental_merkle.AppendOneV1)
    (valid : incremental_merkle.tree_reference.validate_owned tree.inner tree.empty = ok (.Ok ()))
    (h : incremental_merkle.tree_reference.OwnedTree.append_one tree leaf = ok (.Ok (next,receipt))) :
    ∃ capacity, incremental_merkle.POOL_V1_LEAF_CAPACITY = ok capacity ∧ tree.inner.next_leaf_index < capacity := by
  unfold incremental_merkle.tree_reference.OwnedTree.append_one at h
  pv_peel h with capacity hcapacity
  by_cases full : tree.inner.next_leaf_index = capacity
  · rw [if_pos full] at h
    cases h
  · have bounded := PV_RunJoin_RootConstructor31.bound tree.inner tree.empty capacity hcapacity valid
    exact ⟨capacity,hcapacity,by scalar_tac⟩
#print axioms owned

theorem nonfull [ExternalLinear] (tree next : incremental_merkle.IncrementalMerkleTreeV1)
    (leaf : Digest) (roots : Roots) (receipt : incremental_merkle.AppendOneV1)
    (h : incremental_merkle.IncrementalMerkleTreeV1.append_one_with_empty_roots tree leaf roots = ok (.Ok (next,receipt))) :
    ∃ capacity, incremental_merkle.POOL_V1_LEAF_CAPACITY = ok capacity ∧ tree.next_leaf_index < capacity := by
  unfold incremental_merkle.IncrementalMerkleTreeV1.append_one_with_empty_roots at h
  pv_peel h with made hmade
  cases made with
  | Err error =>
    change (ok (.Err error) : Result (core.result.Result _ _)) = ok (.Ok (next,receipt)) at h
    cases h
  | Ok constructed =>
    have frame := construct tree.next_leaf_index tree.root tree.frontier roots constructed hmade
    have validated := PV_RunJoin_RootConstructor31.owned _ _ _ _ constructed hmade
    have valid : incremental_merkle.tree_reference.validate_owned constructed.inner constructed.empty = ok (.Ok ()) := by
      rw [frame.1,frame.2]
      exact validated
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at h
    pv_peel h with appended happend
    cases appended with
    | Err error =>
      change (ok (.Err error) : Result (core.result.Result _ _)) = ok (.Ok (next,receipt)) at h
      cases h
    | Ok pair =>
      obtain ⟨capacity,hcapacity,small⟩ := owned constructed pair.1 leaf pair.2 valid happend
      exact ⟨capacity,hcapacity,by simpa only [frame.1] using small⟩
#print axioms nonfull
end R1Z.PV_RunJoin_AppendCapacity31
