import NND_CheckpointCarrier
set_option autoImplicit false
namespace NND_Carrier
def tree (x : AdapterRw.aspis_statement.pool_v1.incremental_merkle.IncrementalMerkleTreeV1) : RSL.Tree :=
 { next_leaf_index := slot x.next_leaf_index,
   root := digest x.root,
   frontier := frontier x.frontier }
theorem tree_injective : Function.Injective tree := by
 intro x y h
 cases x
 cases y
 simp only [tree,RSL.Tree.mk.injEq,digest_eq_iff,frontier_eq_iff,slot_eq_iff] at h
 exact AdapterRw.aspis_statement.pool_v1.incremental_merkle.IncrementalMerkleTreeV1.mk.injEq.mpr h
@[simp] theorem tree_eq_iff (x y : AdapterRw.aspis_statement.pool_v1.incremental_merkle.IncrementalMerkleTreeV1) : tree x = tree y ↔ x = y :=
 ⟨fun h => tree_injective h,congrArg tree⟩
#print axioms tree_injective
#print axioms tree_eq_iff
end NND_Carrier
