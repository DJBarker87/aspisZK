import NDO_JGk_TX2_NativeLeaves
import Port4B_KeyDecode
import NDO_JGk_TX2_FrontierOrder
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGk_TX2_LeafIteration
open Aeneas Aeneas.Std Result MultiproofConeRef
open AspisV8R19.SqueezeOracleBridge
theorem opening0 (i : Fin 12) :
    Port4B_NativeLeaf.openingIndex 10#usize
      (MultiproofConeSortOrder.packed JGk_TX2_FrontierOrder.q 1 0 (10+i.val))=
        JFo_Opening.cursor (JFn_Values.position i) := by
  apply UScalar.eq_of_val_eq
  have member : 10+i.val ∈ OraclePortSelectedDraft.batchPositions 1 := by
    simp only [OraclePortSelectedDraft.batchPositions,show ¬(1:Nat)=0 from by decide,if_false,List.mem_map]
    exact ⟨i.val,List.mem_range.mpr i.isLt,by omega⟩
  exact (Port4B_KeyDecode.packed JGk_TX2_FrontierOrder.q 1 0 (10+i.val) member 10#usize rfl).2
#print axioms opening0

theorem source0 {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (i : Fin 12) (pos : Usize) (keys : Array U64 16#usize) (root : Array U8 32#usize)
    (s : reference.Scratch) (more : pos<12#usize) (room : s.n.val<16)
    (keyRead : Array.index_usize keys pos=ok
      (MultiproofConeSortOrder.packed JGk_TX2_FrontierOrder.q 1 0 (10+i.val))) :
    Port3_NativeBatchBody.verifier.candidate.batch_tree_loop.body
      (Port3_BatchStd.install Port4B_Install.leaves) (JGc_TX2_RealLeaves.dictionary D)
      JFx_NativeBytes.proof root 0#usize hash 10#usize 12#usize 3#usize
      keys s.idx s.val s.n pos=
        (do let out ← reference.leaf_step s
              (Port4B_NativeLeaf.decodedIndex (MultiproofConeSortOrder.packed JGk_TX2_FrontierOrder.q 1 0 (10+i.val)))
              (encodeState (JGk_TX2_NativeLeaves.value0 i))
            ok (Port4B_LeafStep.project s (Usize.wrapping_add pos 1#usize) out)) := by
  apply Port4B_NativeLeaf.step Port4B_Install.leaves (JGc_TX2_RealLeaves.dictionary D) hash
    JFx_NativeBytes.proof root 0#usize 10#usize 12#usize 3#usize pos keys s
    _ (JFo_Opening.value (JFn_Values.position i)) _ more room keyRead
  · change Port4B_Opening.opening _ _=_
    rw [opening0]
    exact JFo_Opening.call _
  · exact JGk_TX2_NativeLeaves.source0 D hash i
#print axioms source0
theorem opening1 (i : Fin 12) :
    Port4B_NativeLeaf.openingIndex 10#usize
      (MultiproofConeSortOrder.packed JGk_TX2_FrontierOrder.q 1 1 (10+i.val))=
        JFo_Opening.cursor (JFn_Values.position i) := by
  apply UScalar.eq_of_val_eq
  have member : 10+i.val ∈ OraclePortSelectedDraft.batchPositions 1 := by
    simp only [OraclePortSelectedDraft.batchPositions,show ¬(1:Nat)=0 from by decide,if_false,List.mem_map]
    exact ⟨i.val,List.mem_range.mpr i.isLt,by omega⟩
  exact (Port4B_KeyDecode.packed JGk_TX2_FrontierOrder.q 1 1 (10+i.val) member 10#usize rfl).2
#print axioms opening1

theorem source1 {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (i : Fin 12) (pos : Usize) (keys : Array U64 16#usize) (root : Array U8 32#usize)
    (s : reference.Scratch) (more : pos<12#usize) (room : s.n.val<16)
    (keyRead : Array.index_usize keys pos=ok
      (MultiproofConeSortOrder.packed JGk_TX2_FrontierOrder.q 1 1 (10+i.val))) :
    Port3_NativeBatchBody.verifier.candidate.batch_tree_loop.body
      (Port3_BatchStd.install Port4B_Install.leaves) (JGc_TX2_RealLeaves.dictionary D)
      JFx_NativeBytes.proof root 1#usize hash 10#usize 12#usize 4#usize
      keys s.idx s.val s.n pos=
        (do let out ← reference.leaf_step s
              (Port4B_NativeLeaf.decodedIndex (MultiproofConeSortOrder.packed JGk_TX2_FrontierOrder.q 1 1 (10+i.val)))
              (encodeState (JGk_TX2_NativeLeaves.value1 i))
            ok (Port4B_LeafStep.project s (Usize.wrapping_add pos 1#usize) out)) := by
  apply Port4B_NativeLeaf.step Port4B_Install.leaves (JGc_TX2_RealLeaves.dictionary D) hash
    JFx_NativeBytes.proof root 1#usize 10#usize 12#usize 4#usize pos keys s
    _ (JFo_Opening.value (JFn_Values.position i)) _ more room keyRead
  · change Port4B_Opening.opening _ _=_
    rw [opening1]
    exact JFo_Opening.call _
  · exact JGk_TX2_NativeLeaves.source1 D hash i
#print axioms source1
theorem opening2 (i : Fin 12) :
    Port4B_NativeLeaf.openingIndex 10#usize
      (MultiproofConeSortOrder.packed JGk_TX2_FrontierOrder.q 1 2 (10+i.val))=
        JFo_Opening.cursor (JFn_Values.position i) := by
  apply UScalar.eq_of_val_eq
  have member : 10+i.val ∈ OraclePortSelectedDraft.batchPositions 1 := by
    simp only [OraclePortSelectedDraft.batchPositions,show ¬(1:Nat)=0 from by decide,if_false,List.mem_map]
    exact ⟨i.val,List.mem_range.mpr i.isLt,by omega⟩
  exact (Port4B_KeyDecode.packed JGk_TX2_FrontierOrder.q 1 2 (10+i.val) member 10#usize rfl).2
#print axioms opening2

theorem source2 {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (i : Fin 12) (pos : Usize) (keys : Array U64 16#usize) (root : Array U8 32#usize)
    (s : reference.Scratch) (more : pos<12#usize) (room : s.n.val<16)
    (keyRead : Array.index_usize keys pos=ok
      (MultiproofConeSortOrder.packed JGk_TX2_FrontierOrder.q 1 2 (10+i.val))) :
    Port3_NativeBatchBody.verifier.candidate.batch_tree_loop.body
      (Port3_BatchStd.install Port4B_Install.leaves) (JGc_TX2_RealLeaves.dictionary D)
      JFx_NativeBytes.proof root 2#usize hash 10#usize 12#usize 5#usize
      keys s.idx s.val s.n pos=
        (do let out ← reference.leaf_step s
              (Port4B_NativeLeaf.decodedIndex (MultiproofConeSortOrder.packed JGk_TX2_FrontierOrder.q 1 2 (10+i.val)))
              (encodeState (JGc_TX2_RealLeaves.value i))
            ok (Port4B_LeafStep.project s (Usize.wrapping_add pos 1#usize) out)) := by
  apply Port4B_NativeLeaf.step Port4B_Install.leaves (JGc_TX2_RealLeaves.dictionary D) hash
    JFx_NativeBytes.proof root 2#usize 10#usize 12#usize 5#usize pos keys s
    _ (JFo_Opening.value (JFn_Values.position i)) _ more room keyRead
  · change Port4B_Opening.opening _ _=_
    rw [opening2]
    exact JFo_Opening.call _
  · exact JGc_TX2_RealLeaves.source D hash i
#print axioms source2
end AspisR1.JGk_TX2_LeafIteration
end
