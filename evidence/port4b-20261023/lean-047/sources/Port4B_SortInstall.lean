import Port4B_TreeCuts

set_option autoImplicit false
noncomputable section
namespace AspisR1.Port4B_SortInstall
open Aeneas Aeneas.Std Result
open MultiproofSortRef

def install (base : Port3_NativeBatchBody.Ops) : Port3_NativeBatchBody.Ops :=
  {Port4B_LeafInstall.install base with op5:=fun raw n => sort_reference.sort_rows raw 1#usize n}

/-- The actual returned sorted array supplies every physical key read, in
frozen order, including query-index ties. The sole carrier gate is the raw
packed-key prefix produced from the physical Prepared queries. -/
theorem key_stream (base : Port3_NativeBatchBody.Ops)
    (q : Fin 22 → Fin 262144) (batch kind : Nat)
    (raw sorted : Array U64 16#usize) (n : Usize) (bound : n.val≤16) (positive : 0<n.val)
    (initial : raw.val.take n.val=(OraclePortSelectedDraft.batchPositions batch).map
      (MultiproofConeSortOrder.packed q batch kind))
    (returned : (install base).op5 raw n=ok sorted) :
    (OraclePortFrozenOrder.sortedPositions q batch kind).length=n.val ∧
    Port4B_LeafLoop.KeyStream q batch kind sorted 0#usize
      (OraclePortFrozenOrder.sortedPositions q batch kind) := by
  obtain ⟨out,run,front,suffix⟩ := MultiproofConeSortOrder.sorted_positions q batch kind raw n bound initial
  rw [MultiproofConeSortOrder.source_start_one raw n positive] at run
  have same : out=sorted := Result.ok.inj (run.symm.trans returned)
  subst out
  have length := congrArg List.length initial
  simp only [List.length_take,raw.property,List.length_map] at length
  change min n.val 16=(OraclePortSelectedDraft.batchPositions batch).length at length
  rw [Nat.min_eq_left bound] at length
  have count : (OraclePortFrozenOrder.sortedPositions q batch kind).length=n.val := by
    simpa only [OraclePortFrozenOrder.sortedPositions,List.length_mergeSort] using length.symm
  refine ⟨count,?_⟩
  intro cursor j hj value
  have jn : j<n.val := by omega
  have read := congrArg (fun xs : List U64 => xs[j]?) front
  simp only [List.getElem?_take_of_lt jn,List.getElem?_map,List.getElem?_eq_getElem hj,
    Option.map_some] at read
  change (match sorted.val[cursor.val]? with | none => fail .arrayOutOfBounds | some x => ok x)=_
  have cv : cursor.val=j := by change cursor.val=0+j at value;omega
  rw [cv,read]

#print axioms key_stream
end AspisR1.Port4B_SortInstall
end
