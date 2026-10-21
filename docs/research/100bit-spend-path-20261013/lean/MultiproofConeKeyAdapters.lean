import MultiproofConeSortOrder

set_option autoImplicit false
namespace AspisR1.MultiproofConeKeyAdapters
open Aeneas Aeneas.Std Result MultiproofSortRef
open OraclePortFrozenOrder OraclePortSelectedDraft MultiproofConeSortOrder

/-- Reached batch positions use an absolute opening ordinal but store its
batch-relative ordinal in the low byte. -/
theorem position_bounds (batch pos : Nat) (mem : pos∈batchPositions batch) :
    (if batch=0 then 0 else 10)≤pos ∧ pos<22 := by
  unfold batchPositions at mem
  split at mem
  next h => simp only [List.mem_range] at mem;simp [h];omega
  next h =>
    simp only [List.mem_map,List.mem_range] at mem
    obtain ⟨i,hi,rfl⟩ := mem
    simp [h];omega

/-- Decoding the high key field returns the exact query-derived tree index. -/
theorem packed_index (q : Fin 22 → Fin 262144) (batch kind pos : Nat)
    (mem : pos∈batchPositions batch) :
    (packed q batch kind pos).val/256=index q kind pos := by
  have b := position_bounds batch pos mem
  simp [packed,Nat.mod_eq_of_lt b.2]
  omega

/-- Decoding the low byte and rebasing it selects the original absolute
opening, including ties in the query index and the resumed batch. -/
theorem packed_opening (q : Fin 22 → Fin 262144) (batch kind pos : Nat)
    (mem : pos∈batchPositions batch) :
    (if batch=0 then 0 else 10)+(packed q batch kind pos).val%256=pos := by
  have b := position_bounds batch pos mem
  simp [packed,Nat.mod_eq_of_lt b.2]
  omega

/-- Membership survives sorting, so the key adapters apply to every reached
iteration rather than requiring a separate per-iteration range assumption. -/
theorem sorted_member (q : Fin 22 → Fin 262144) (batch kind pos : Nat)
    (mem : pos∈sortedPositions q batch kind) : pos∈batchPositions batch := by
  exact List.mem_mergeSort.mp mem

/-- Exact index AND opening projections of the actual extracted sorted prefix.
The initial batch_keys equation is the independently certified source cut. -/
theorem sorted_stream (q : Fin 22 → Fin 262144) (batch kind : Nat)
    (keys : Array U64 16#usize) (n : Usize) (bound : n.val≤16)
    (initial : keys.val.take n.val=(batchPositions batch).map (packed q batch kind)) :
    ∃ out, sort_reference.sort_rows keys 0#usize n=ok out ∧
      (out.val.take n.val).map (fun k => (k.val/256,
        (if batch=0 then 0 else 10)+k.val%256)) =
      (sortedPositions q batch kind).map (fun pos => (index q kind pos,pos)) ∧
      out.val.drop n.val=keys.val.drop n.val := by
  obtain ⟨out,eq,front,suffix⟩ := sorted_positions q batch kind keys n bound initial
  refine ⟨out,eq,?_,suffix⟩
  rw [front,List.map_map]
  apply List.map_congr_left
  intro pos mem
  have b := sorted_member q batch kind pos mem
  exact Prod.ext (packed_index q batch kind pos b) (packed_opening q batch kind pos b)

#print axioms position_bounds
#print axioms packed_index
#print axioms packed_opening
#print axioms sorted_member
#print axioms sorted_stream
end AspisR1.MultiproofConeKeyAdapters
