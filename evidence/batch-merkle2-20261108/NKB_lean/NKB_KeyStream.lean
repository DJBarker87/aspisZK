import NKB_SortProducer
import MultiproofConeKeyAdapters

set_option autoImplicit false
namespace NKB_KeyStream
open Aeneas Aeneas.Std Result AspisR1
open OraclePortFrozenOrder OraclePortSelectedDraft

def lo (batch : Nat) : Usize := if batch=0 then 0#usize else 10#usize
def count (batch : Nat) : Usize := if batch=0 then 10#usize else 12#usize

theorem positive (batch : Nat) : 0<(count batch).val ∧ (count batch).val≤12 := by
 unfold count;split <;> decide

theorem built (raw : Array U32 22#usize) (batch : Nat) (kind : Usize)
    (kindBound : kind.val<3) (batchBound : batch<2)
    (canonical : ∀ j,j<22 → raw.val[j]!.val<262144) :
 NJS_Extract.verifier.candidate.batch_keys raw (lo batch) (count batch) kind=
   ok (Port4B_KeyInstall.keyArray raw batch kind.val) := by
 by_cases zero : batch=0
 · subst batch
   exact NKB_SortProducer.tx1_keys raw kind kindBound canonical
 · have one : batch=1 := by omega
   subst batch
   exact NKB_SortProducer.tx2_keys raw kind kindBound canonical

theorem initial (raw : Array U32 22#usize) (batch : Nat) (kind : Usize) :
 (Port4B_KeyInstall.keyArray raw batch kind.val).val.take (count batch).val=
   (batchPositions batch).map (MultiproofConeSortOrder.packed (Port4B_KeyInstall.queries raw) batch kind.val) := by
 have len : (Port4B_KeyInstall.prefixKeys raw batch kind.val).length=(count batch).val := by
   simp only [Port4B_KeyInstall.prefixKeys,List.length_map,batchPositions,count]
   split <;> simp
 change (Port4B_KeyInstall.prefixKeys raw batch kind.val++
   List.replicate (16-(Port4B_KeyInstall.prefixKeys raw batch kind.val).length) 0#u64).take (count batch).val=
   Port4B_KeyInstall.prefixKeys raw batch kind.val
 rw [←len,List.take_append]
 simp only [List.take_length,Nat.sub_self,List.take_zero,List.append_nil]

/-- Actual batch_keys THEN actual sort at the SAME raw queries and batch.
The result supplies both decoded index and absolute opening position, including
folded ties; no child success, independently selected keys or arbitrary q is a
hypothesis. It is a complete key-producer segment, not a whole batch root. -/
theorem source (raw : Array U32 22#usize) (batch : Nat) (kind : Usize)
    (kindBound : kind.val<3) (batchBound : batch<2)
    (canonical : ∀ j,j<22 → raw.val[j]!.val<262144) :
 ∃ out,
 (do let keys ← NJS_Extract.verifier.candidate.batch_keys raw (lo batch) (count batch) kind
     NJS_Extract.verifier.candidate.sort_batch_keys keys (count batch))=ok out ∧
 (out.val.take (count batch).val).map (fun key =>
   (key.val/256,(if batch=0 then 0 else 10)+key.val%256))=
   (sortedPositions (Port4B_KeyInstall.queries raw) batch kind.val).map
     (fun pos => (index (Port4B_KeyInstall.queries raw) kind.val pos,pos)) ∧
 out.val.drop (count batch).val=
   (Port4B_KeyInstall.keyArray raw batch kind.val).val.drop (count batch).val := by
 have pos := positive batch
 obtain ⟨out,run,projection,frame⟩ := MultiproofConeKeyAdapters.sorted_stream
   (Port4B_KeyInstall.queries raw) batch kind.val
   (Port4B_KeyInstall.keyArray raw batch kind.val) (count batch) (by omega) (initial raw batch kind)
 refine ⟨out,?_,projection,frame⟩
 rw [built raw batch kind kindBound batchBound canonical]
 simp only [bind_tc_ok]
 rw [NJS_Sort.source _ _ pos.1 (by omega),←MultiproofConeSortOrder.source_start_one _ _ pos.1]
 exact run

#print axioms positive
#print axioms built
#print axioms initial
#print axioms source
end NKB_KeyStream
