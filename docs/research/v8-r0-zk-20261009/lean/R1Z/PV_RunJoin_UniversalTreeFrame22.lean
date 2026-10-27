import R1Z.PV_Src_CompilerTactic
import R1Z.PV_Src_NativeInput
set_option autoImplicit false
namespace R1Z.PV_RunJoin_UniversalTreeFrame22
open Aeneas Aeneas.Std Result
open BuilderForestAdmissionPort BuilderForestAdmissionPort.pool_v1 BuilderRecordsFields
abbrev Digest := Array U32 8#usize
abbrev Frontier := Array Digest 20#usize
abbrev Roots := Array Digest 21#usize

/-- A successful owned constructor preserves every supplied tree field. -/
theorem construct [ExternalLinear] (index : U64) (root : Digest) (frontier : Frontier)
    (roots : Roots) (tree : incremental_merkle.tree_reference.OwnedTree)
    (h : incremental_merkle.tree_reference.OwnedTree.from_parts index root frontier roots =
      ok (.Ok tree)) :
    tree.inner = ⟨index,root,frontier⟩ ∧ tree.empty = roots := by
  unfold incremental_merkle.tree_reference.OwnedTree.from_parts at h
  repeat' first
    | (pv_peel h with value hvalue)
    | exact False.elim (PV_Src_ResultControl.error_ne_ok _ _ h)
    | exact False.elim (PV_Src_ResultControl.same_residual_ne_ok _ _ h)
    | (have _test : core.ops.control_flow.ControlFlow _ _ := value; cases value)
    | (cases h; exact ⟨rfl,rfl⟩)
#print axioms construct

/-- The universal append wrapper returns the same incremented index and
receipt fields on both its final-level and reconstruction branches. -/
theorem append [ExternalLinear] (tree next : incremental_merkle.tree_reference.OwnedTree)
    (leaf : Digest) (receipt : incremental_merkle.AppendOneV1)
    (h : incremental_merkle.tree_reference.OwnedTree.append_one tree leaf = ok (.Ok (next,receipt))) :
    next.inner.next_leaf_index = U64.wrapping_add tree.inner.next_leaf_index 1#u64 ∧
      receipt.leaf_index = tree.inner.next_leaf_index ∧
      receipt.root_sequence = next.inner.next_leaf_index ∧ receipt.root = next.inner.root := by
  unfold incremental_merkle.tree_reference.OwnedTree.append_one at h
  simp only [lift,bind_tc_ok] at h
  repeat' first
    | (pv_peel h with value hvalue)
    | exact False.elim (PV_Src_ResultControl.error_ne_ok _ _ h)
    | exact False.elim (PV_Src_ResultControl.same_residual_ne_ok _ _ h)
    | (have _test : core.ops.control_flow.ControlFlow _ _ := value; cases value)
    | (have _test : _ × _ := value; rcases value with ⟨value,rest⟩)
    | (split at h)
    | (cases h; exact ⟨rfl,rfl,rfl,rfl⟩)
#print axioms append
end R1Z.PV_RunJoin_UniversalTreeFrame22
