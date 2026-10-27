from pathlib import Path
P=Path(__file__).resolve().parent;R=P.parents[1]
for t in range(3):
 ns=f'JGu_LeafIteration{t}'
 imports=''.join(f'import JGu_M{t}LeafSources{j:02}\n' for j in (range(0,10,2) if t==0 else [0]))
 s=imports+f'''import JGu_Keys
import JGc_TX2_RealLeaves
import Port4B_KeyDecode
set_option autoImplicit false
noncomputable section
namespace AspisR1.{ns}
open Aeneas Aeneas.Std Result MultiproofConeRef
open AspisV8R19.SqueezeOracleBridge
'''
 s+='def opening (i : Fin 10) : Slice U8 := JFo_Opening.value ⟨i.val,by have := i.isLt;omega⟩\n'
 s+=f'def value (i : Fin 10) : AspisV8R19.SourceDuplexStep.State := match i.val with\n'
 for j in range(9):s+=f'  | {j} => JGr_M{t}Roots.value{j:03}\n'
 s+=f'  | _ => JGr_M{t}Roots.value009\n'
 s+=f'''theorem leaf {{Hash : Type}} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash) (i : Fin 10) :
    Port4B_LeafCode.native (JGc_TX2_RealLeaves.dictionary D) hash {t}#usize (opening i)=ok (encodeState (value i)) := by
  fin_cases i
'''
 for j in range(10):s+=f'  · exact JGu_M{t}Leaf{j:02}.source D hash\n'
 s+='#print axioms leaf\n'
 s+=f'''theorem opening_read (i : Fin 10) :
    Port4B_Opening.opening JFx_NativeBytes.proof (Port4B_NativeLeaf.openingIndex 0#usize
      (MultiproofConeSortOrder.packed JGr_Keys.q 0 {t} i.val))=ok (opening i) := by
  have member : i.val ∈ OraclePortSelectedDraft.batchPositions 0 := List.mem_range.mpr i.isLt
  have decoded := (Port4B_KeyDecode.packed JGr_Keys.q 0 {t} i.val member 0#usize rfl).2
  have cursor : Port4B_NativeLeaf.openingIndex 0#usize (MultiproofConeSortOrder.packed JGr_Keys.q 0 {t} i.val)=UScalar.ofNat i.val (by have := i.isLt;scalar_tac) := UScalar.eq_of_val_eq decoded
  have read := JFo_Opening.call (⟨i.val,by have := i.isLt;omega⟩ : Fin 22)
  have same : JFo_Opening.cursor (⟨i.val,by have := i.isLt;omega⟩ : Fin 22)=UScalar.ofNat i.val (by have := i.isLt;scalar_tac) := rfl
  rw [same] at read
  rw [cursor]
  exact read
'''
 s+='#print axioms opening_read\n'
 s+=f'''theorem source {{Hash : Type}} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (i : Fin 10) (pos : Usize) (keys : Array U64 16#usize) (root : Array U8 32#usize)
    (s : reference.Scratch) (more : pos<10#usize) (room : s.n.val<16)
    (keyRead : Array.index_usize keys pos=ok (MultiproofConeSortOrder.packed JGr_Keys.q 0 {t} i.val)) :
    Port3_NativeBatchBody.verifier.candidate.batch_tree_loop.body
      (Port3_BatchStd.install Port4B_Install.leaves) (JGc_TX2_RealLeaves.dictionary D)
      JFx_NativeBytes.proof root {t}#usize hash 0#usize 10#usize {t}#usize keys s.idx s.val s.n pos=
        (do let out ← reference.leaf_step s
              (Port4B_NativeLeaf.decodedIndex (MultiproofConeSortOrder.packed JGr_Keys.q 0 {t} i.val))
              (encodeState (value i))
            ok (Port4B_LeafStep.project s (Usize.wrapping_add pos 1#usize) out)) := by
  apply Port4B_NativeLeaf.step Port4B_Install.leaves (JGc_TX2_RealLeaves.dictionary D) hash
    JFx_NativeBytes.proof root {t}#usize 0#usize 10#usize {t}#usize pos keys s
    _ (opening i) _ more room keyRead
  · exact opening_read i
  · exact leaf D hash i
#print axioms source
end AspisR1.{ns}
end
'''
 (R/f'lean/{ns}.lean').write_text(s)
