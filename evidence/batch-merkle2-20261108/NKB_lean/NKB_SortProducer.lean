import NJS_Keys
import NJS_Sort
import MultiproofConeSortTotal

set_option autoImplicit false
namespace NKB_SortProducer
open Aeneas Aeneas.Std Result AspisR1 MultiproofSortRef

/-- The actual emitted sort produces the sorted prefix and preserves every
inactive packed key. The input is the caller's returned batch_keys array. -/
theorem sorted (raw : Array U64 16#usize) (n : Usize)
    (positive : 0<n.val) (bound : n.val≤12) :
 ∃ out, NJS_Extract.verifier.candidate.sort_batch_keys raw n=ok out ∧
   out.val.Perm raw.val ∧ (out.val.take n.val).Pairwise (·≤·) ∧
   out.val.drop n.val=raw.val.drop n.val := by
 obtain ⟨out,run,perm,order,frame⟩ := MultiproofConeSortTotal.sort_rows_total
   n.val raw 0#usize n (by simp) (by omega) (by simp)
 rw [MultiproofConeSortOrder.source_start_one raw n positive] at run
 exact ⟨out,(NJS_Sort.source raw n positive (by omega)).trans run,perm,order,frame⟩

/-- Exact TX2 key builder, instantiated at its own twelve-query arguments. -/
theorem tx2_keys (queries : Array U32 22#usize) (tree : Usize) (kind : tree.val<3)
    (canonical : ∀ j,j<22 → queries.val[j]!.val<262144) :
 NJS_Extract.verifier.candidate.batch_keys queries 10#usize 12#usize tree=
   ok (Port4B_KeyInstall.keyArray queries 1 tree.val) := by
 rw [NJS_Keys.source queries 10#usize 12#usize tree (Or.inr ⟨rfl,rfl⟩) kind canonical]
 simp only [Port4B_KeyInstall.build,show ¬10#usize=0#usize by decide,if_false,
   OraclePortSelectedDraft.batchPositions,show ¬(1:Nat)=0 by decide,if_false,
   List.length_map,List.length_range,show (12#usize).val=12 by rfl,
   eq_self_iff_true,or_true,true_and,kind,if_pos,↓reduceDIte]

/-- Exact TX1 key builder, kept separate from the TX2 occurrence. -/
theorem tx1_keys (queries : Array U32 22#usize) (tree : Usize) (kind : tree.val<3)
    (canonical : ∀ j,j<22 → queries.val[j]!.val<262144) :
 NJS_Extract.verifier.candidate.batch_keys queries 0#usize 10#usize tree=
   ok (Port4B_KeyInstall.keyArray queries 0 tree.val) := by
 rw [NJS_Keys.source queries 0#usize 10#usize tree (Or.inl ⟨rfl,rfl⟩) kind canonical]
 simp only [Port4B_KeyInstall.build,if_pos rfl,OraclePortSelectedDraft.batchPositions,
   List.length_range,show (10#usize).val=10 by rfl,eq_self_iff_true,true_or,true_and,kind,if_pos,↓reduceDIte]

#print axioms sorted
#print axioms tx2_keys
#print axioms tx1_keys
end NKB_SortProducer
