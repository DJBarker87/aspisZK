import NBJ_Address
import Port4B_SortInstall

set_option autoImplicit false
noncomputable section
namespace AspisR1.NBJ_Keys
open Aeneas Aeneas.Std Result MultiproofSortRef
open OraclePortSelectedDraft MultiproofConeSortOrder

/-- Complete source producer feeds the installed sort from its actual prefix.
The final sorted array is constructed, never supplied as an assumption. -/
theorem producer_sorted (raw : Array U32 22#usize) (batch kind : Nat)
    (n : Usize) (count : n.val = (batchPositions batch).length) :
    ∃ sorted,
      sort_reference.sort_rows (NBI_Keys.producer raw batch kind) 1#usize n = ok sorted ∧
      sorted.val.take n.val =
        (OraclePortFrozenOrder.sortedPositions (Port4B_KeyInstall.queries raw) batch kind).map
          (packed (Port4B_KeyInstall.queries raw) batch kind) ∧
      sorted.val.drop n.val = List.replicate (16-n.val) 0#u64 := by
  have len : (Port4B_KeyInstall.prefixKeys raw batch kind).length = n.val := by
    simpa only [Port4B_KeyInstall.prefixKeys,List.length_map] using count.symm
  have bound : n.val ≤ 16 := by
    rw [←len]
    exact Port4B_KeyInstall.prefix_bound raw batch kind
  have positive : 0 < n.val := by
    rw [count]
    unfold batchPositions
    split <;> simp
  have initial : (Port4B_KeyInstall.keyArray raw batch kind).val.take n.val =
      (batchPositions batch).map (packed (Port4B_KeyInstall.queries raw) batch kind) := by
    change (Port4B_KeyInstall.prefixKeys raw batch kind ++
      List.replicate (16-(Port4B_KeyInstall.prefixKeys raw batch kind).length) 0#u64).take n.val = _
    rw [←len,List.take_left]
    rfl
  obtain ⟨sorted,run,front,tail⟩ := sorted_positions
    (Port4B_KeyInstall.queries raw) batch kind
    (Port4B_KeyInstall.keyArray raw batch kind) n bound initial
  rw [source_start_one _ n positive] at run
  refine ⟨sorted,?_,front,?_⟩
  · rw [NBI_Keys.producer_eq]
    exact run
  · rw [tail]
    change (Port4B_KeyInstall.prefixKeys raw batch kind ++
      List.replicate (16-(Port4B_KeyInstall.prefixKeys raw batch kind).length) 0#u64).drop n.val = _
    rw [←len,List.drop_left]

#print axioms producer_sorted
end AspisR1.NBJ_Keys
end
