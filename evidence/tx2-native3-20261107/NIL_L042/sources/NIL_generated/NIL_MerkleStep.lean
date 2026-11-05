import NID_MerkleLeafPacket
import Port4B_KeyDecode
import Port4B_NativeLeaf
import Port4B_LeafInstall
set_option autoImplicit false
noncomputable section
namespace NIL_MerkleStep
open Aeneas Aeneas.Std Result ControlFlow AspisR1 AspisR1Stage2
open CheckpointBytes5Effect Port4B_NativeLeaf Port4B_LeafStep MultiproofConeRef

theorem selected {H : Type} (D : aspis_core.digest.Digest32 H) (hash : H)
 (base : Port3_NativeBatchBody.Ops) (proof : Slice U8) (length : proof.val.length=57607)
 (root : Array U8 32#usize) (tree position slot : Usize)
 (q : Fin 22 → Fin 262144) (original : Nat)
 (member : original∈OraclePortSelectedDraft.batchPositions 1)
 (keys : Array U64 16#usize) (s : reference.Scratch)
 (more : position<12#usize)
 (keyRead : Array.index_usize keys position=ok (MultiproofConeSortOrder.packed q 1 tree.val original))
 (before : Log) :
 ∃ view,
   Port4B_Opening.opening proof (openingIndex 10#usize (MultiproofConeSortOrder.packed q 1 tree.val original))=ok view ∧
   view.val.length=832 ∧
   (openingIndex 10#usize (MultiproofConeSortOrder.packed q 1 tree.val original)).val=original ∧
   Port3_NativeBatchBody.verifier.candidate.batch_tree_loop.body
    (Port3_BatchStd.install (Port4B_LeafInstall.install base)) D proof root tree hash
    10#usize 12#usize slot keys s.idx s.val s.n position=
    (do let leaf ← D.digest hash (Port4B_LeafCode.input tree view)
        post s.idx s.val s.n (decodedIndex (MultiproofConeSortOrder.packed q 1 tree.val original))
         leaf (Usize.wrapping_add position 1#usize)) ∧
   run D hash (Port4B_LeafCode.code tree view) before=
    (do let leaf ← D.digest hash (Port4B_LeafCode.input tree view)
        ok (leaf,before++[(Port4B_LeafCode.input tree view,leaf)])) := by
 have packed := Port4B_KeyDecode.packed q 1 tree.val original member 10#usize rfl
 have bounds := MultiproofConeKeyAdapters.position_bounds 1 original member
 obtain ⟨view,read,width,_,leaf,events⟩ := NID_MerkleLeafPacket.selected D hash proof length
  (openingIndex 10#usize (MultiproofConeSortOrder.packed q 1 tree.val original)) tree
  (by rw [packed.2];exact bounds.2) before
 refine ⟨view,read,width,packed.2,?_,events⟩
 rw [Port4B_NativeLeaf.active (Port4B_LeafInstall.install base) D hash proof root tree
  10#usize 12#usize slot s.n position keys s.idx s.val more]
 simp only [keyRead,Port4B_LeafInstall.install,read,bind_tc_ok,Port4B_LeafCode.native,leaf]

#print axioms selected
end NIL_MerkleStep
