import NNU_MerkleNative
import NNU_MerkleLeaf
import NKB_CanonicalRows
import NKV_ConcreteDomains
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNU_MerkleChildren
open Aeneas Aeneas.Std Result

theorem opening (proof : Slice U8) (i : Usize) :
 NJS_Extract.verifier.candidate.opening proof i=Port4B_Opening.opening proof i := NKB_CanonicalRows.opening proof i

theorem key (raw : Array U32 22#usize) (tree : Usize) (bound : tree.val < 3)
 (canonical : ∀ j, j < 22 → raw.val[j]!.val < 262144) :
 NJS_Extract.verifier.candidate.batch_keys raw 10#usize 12#usize tree=
 Port4B_KeyInstall.build raw 10#usize 12#usize tree :=
 NJS_Keys.source raw 10#usize 12#usize tree (Or.inr ⟨rfl,rfl⟩) bound canonical

theorem sort (keys : Array U64 16#usize) :
 NJS_Extract.verifier.candidate.sort_batch_keys keys 12#usize=
 MultiproofSortRef.sort_reference.sort_rows keys 1#usize 12#usize :=
 NJS_Sort.source keys 12#usize (by decide) (by decide)

theorem slot (proof : Slice U8) (s : Usize) (bound : s.val < 6) :
 NJS_Extract.verifier.candidate.slot NGD_SlotRef.slot_offset proof s=Port4B_SlotInstall.nodeSlot proof s :=
 NJS_Slot.source proof s bound

theorem leaf (env : RSL.Env) (tree : Usize) (view : Slice U8) (width : view.val.length=832) :
 (NKV_ConcreteChildren.ops (LIBB_PartitionEnv.H env)).op6
 (NKV_ConcreteChildren.digest (LIBB_PartitionEnv.H env)) () tree view=
 Port4B_LeafCode.native (VTop_Checkpoint.digest (LIBB_PartitionEnv.digest env)) () tree view := by
 rw [NKV_ConcreteDomains.leaf _ _ () tree view width]
 rw [NNU_MerkleLeaf.source env tree view width]
 rw [Port4B_LeafCode.native,(Port4B_LeafCode.code_exact _ () tree view width []).1]
 rfl
#print axioms opening
#print axioms key
#print axioms sort
#print axioms slot
#print axioms leaf
end AspisR1.NNU_MerkleChildren
end
