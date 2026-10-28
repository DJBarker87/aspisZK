import R1Z.PV_RunJoin_SnapshotRoot31
set_option autoImplicit false
namespace R1Z.PV_RunJoin_RootConstructor31
open Aeneas Aeneas.Std Result BuilderForestAdmissionPort BuilderForestAdmissionPort.pool_v1
open PV_RunJoin_UniversalTreeFrame22

theorem owned [ExternalLinear] (index : U64) (root : Digest) (frontier : Frontier)
    (roots : Roots) (tree : incremental_merkle.tree_reference.OwnedTree)
    (h : incremental_merkle.tree_reference.OwnedTree.from_parts index root frontier roots = ok (.Ok tree)) :
    incremental_merkle.tree_reference.validate_owned ⟨index,root,frontier⟩ roots = ok (.Ok ()) := by
  unfold incremental_merkle.tree_reference.OwnedTree.from_parts at h
  pv_peel h with result hr
  pv_peel h with flow hf
  cases flow with
  | Break residual => exact False.elim (PV_Src_ResultControl.same_residual_ne_ok _ _ h)
  | Continue value =>
    have same := PV_RunJoin_DecoderReturn29.branch_continue result value hf
    cases same
    cases value
    exact hr
#print axioms owned

theorem validated [ExternalLinear] (index : U64) (root : Digest) (frontier : Frontier)
    (roots : Roots) (tree : incremental_merkle.IncrementalMerkleTreeV1)
    (h : incremental_merkle.IncrementalMerkleTreeV1.from_parts_with_empty_roots index root frontier roots = ok (.Ok tree)) :
    incremental_merkle.tree_reference.validate_owned ⟨index,root,frontier⟩ roots = ok (.Ok ()) := by
  unfold incremental_merkle.IncrementalMerkleTreeV1.from_parts_with_empty_roots at h
  pv_peel h with result hr
  cases result with
  | Err error => cases h
  | Ok made => exact owned index root frontier roots made hr
#print axioms validated

theorem bound [ExternalLinear] (tree : incremental_merkle.IncrementalMerkleTreeV1)
    (roots : Roots) (capacity : U64)
    (hcapacity : incremental_merkle.POOL_V1_LEAF_CAPACITY = ok capacity)
    (h : incremental_merkle.tree_reference.validate_owned tree roots = ok (.Ok ())) :
    tree.next_leaf_index ≤ capacity := by
  rw [incremental_merkle.tree_reference.validate_owned,hcapacity] at h
  simp only [bind_tc_ok] at h
  by_contra large
  have outside : tree.next_leaf_index > capacity := by scalar_tac
  rw [if_pos outside] at h
  cases h
#print axioms bound
end R1Z.PV_RunJoin_RootConstructor31
