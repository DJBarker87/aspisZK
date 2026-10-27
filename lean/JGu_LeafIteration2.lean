import JGu_M2LeafSources00
import JGu_Keys
import JGc_TX2_RealLeaves
import Port4B_KeyDecode
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGu_LeafIteration2
open Aeneas Aeneas.Std Result MultiproofConeRef
open AspisV8R19.SqueezeOracleBridge
def opening (i : Fin 10) : Slice U8 := JFo_Opening.value ⟨i.val,by have := i.isLt;omega⟩
def value (i : Fin 10) : AspisV8R19.SourceDuplexStep.State := match i.val with
  | 0 => JGr_M2Roots.value000
  | 1 => JGr_M2Roots.value001
  | 2 => JGr_M2Roots.value002
  | 3 => JGr_M2Roots.value003
  | 4 => JGr_M2Roots.value004
  | 5 => JGr_M2Roots.value005
  | 6 => JGr_M2Roots.value006
  | 7 => JGr_M2Roots.value007
  | 8 => JGr_M2Roots.value008
  | _ => JGr_M2Roots.value009
theorem leaf {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash) (i : Fin 10) :
    Port4B_LeafCode.native (JGc_TX2_RealLeaves.dictionary D) hash 2#usize (opening i)=ok (encodeState (value i)) := by
  fin_cases i
  · exact JGu_M2Leaf00.source D hash
  · exact JGu_M2Leaf01.source D hash
  · exact JGu_M2Leaf02.source D hash
  · exact JGu_M2Leaf03.source D hash
  · exact JGu_M2Leaf04.source D hash
  · exact JGu_M2Leaf05.source D hash
  · exact JGu_M2Leaf06.source D hash
  · exact JGu_M2Leaf07.source D hash
  · exact JGu_M2Leaf08.source D hash
  · exact JGu_M2Leaf09.source D hash
#print axioms leaf
theorem opening_read (i : Fin 10) :
    Port4B_Opening.opening JFx_NativeBytes.proof (Port4B_NativeLeaf.openingIndex 0#usize
      (MultiproofConeSortOrder.packed JGr_Keys.q 0 2 i.val))=ok (opening i) := by
  have member : i.val ∈ OraclePortSelectedDraft.batchPositions 0 := List.mem_range.mpr i.isLt
  have decoded := (Port4B_KeyDecode.packed JGr_Keys.q 0 2 i.val member 0#usize rfl).2
  have cursor : Port4B_NativeLeaf.openingIndex 0#usize (MultiproofConeSortOrder.packed JGr_Keys.q 0 2 i.val)=UScalar.ofNat i.val (by have := i.isLt;scalar_tac) := UScalar.eq_of_val_eq decoded
  have read := JFo_Opening.call (⟨i.val,by have := i.isLt;omega⟩ : Fin 22)
  have same : JFo_Opening.cursor (⟨i.val,by have := i.isLt;omega⟩ : Fin 22)=UScalar.ofNat i.val (by have := i.isLt;scalar_tac) := rfl
  rw [same] at read
  rw [cursor]
  exact read
#print axioms opening_read
theorem source {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (i : Fin 10) (pos : Usize) (keys : Array U64 16#usize) (root : Array U8 32#usize)
    (s : reference.Scratch) (more : pos<10#usize) (room : s.n.val<16)
    (keyRead : Array.index_usize keys pos=ok (MultiproofConeSortOrder.packed JGr_Keys.q 0 2 i.val)) :
    Port3_NativeBatchBody.verifier.candidate.batch_tree_loop.body
      (Port3_BatchStd.install Port4B_Install.leaves) (JGc_TX2_RealLeaves.dictionary D)
      JFx_NativeBytes.proof root 2#usize hash 0#usize 10#usize 2#usize keys s.idx s.val s.n pos=
        (do let out ← reference.leaf_step s
              (Port4B_NativeLeaf.decodedIndex (MultiproofConeSortOrder.packed JGr_Keys.q 0 2 i.val))
              (encodeState (value i))
            ok (Port4B_LeafStep.project s (Usize.wrapping_add pos 1#usize) out)) := by
  apply Port4B_NativeLeaf.step Port4B_Install.leaves (JGc_TX2_RealLeaves.dictionary D) hash
    JFx_NativeBytes.proof root 2#usize 0#usize 10#usize 2#usize pos keys s
    _ (opening i) _ more room keyRead
  · exact opening_read i
  · exact leaf D hash i
#print axioms source
end AspisR1.JGu_LeafIteration2
end
