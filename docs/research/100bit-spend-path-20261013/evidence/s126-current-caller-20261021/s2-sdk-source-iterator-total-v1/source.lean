import S2SdkSourceIteratorV1
import S2SdkOwnedBorrowTotalV1
import S2StdAnySourceTotalV1
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace AspisS2SdkIterator
open AspisS2OwnedStage1.SdkReference
open AspisS2StdAnySource

/-- Valid native view of a suffix of the complete guarded account buffer. -/
def Valid (sdk : OwnedSdk) (ptr endp : DataPointer) : Prop :=
  ptr.slot=endp.slot ∧ ptr.offset.val≤endp.offset.val ∧
  ∃ cell, sdk.data_cells.val[ptr.slot.val]?=some cell ∧
    endp.offset.val=cell.bytes.val.length

def remaining (sdk : OwnedSdk) (ptr : DataPointer) (_endp : DataPointer) : List U8 :=
  match sdk.data_cells.val[ptr.slot.val]? with
  | none => []
  | some cell => cell.bytes.val.drop ptr.offset.val

def wrap (iter : SourceIterator) : SourceIter DataPointer DataPointer :=
  ⟨iter.ptr,iter.end_or_len,()⟩

def next (sdk : OwnedSdk) (iter : SourceIter DataPointer DataPointer) :
    Result ((Option U8) × SourceIter DataPointer DataPointer) := do
  let (out,iter') ← source_next sdk ⟨iter.ptr,iter.end_or_len⟩
  ok (out,wrap iter')

private theorem read_cell (sdk : OwnedSdk) (slot : Usize) (cell : OwnedDataCell)
    (which : sdk.data_cells.val[slot.val]?=some cell) :
    alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice OwnedDataCell)
      sdk.data_cells slot=ok cell := by
  have valid : slot.val<sdk.data_cells.val.length := by
    by_contra invalid
    have absent : sdk.data_cells.val[slot.val]?=none :=
      List.getElem?_eq_none.mpr (by omega)
    rw [which] at absent
    cases absent
  obtain ⟨actual,hactual,hread,_⟩ := BorrowTotal.cell_operations_total sdk slot valid
  rw [List.getElem?_eq_getElem valid] at which
  have equal : actual=cell := hactual.trans (Option.some.inj which)
  simpa only [equal] using hread

private theorem add_total (offset : Usize) (bound : offset.val+1≤Usize.max) :
    ∃ result : Usize, (offset+1#usize : Result Usize)=ok result ∧
      result.val=offset.val+1 := by
  apply WP.spec_imp_exists
  apply UScalar.add_spec
  rw [UScalar.max_USize_eq]
  exact bound

/-- TOTAL one-step instance for the complete emitted owned-SDK next function.
All assertions, both indexing operations and the cursor addition are derived
from the constructor/loop invariant; no operation-success premise is retained. -/
theorem next_reads (sdk : OwnedSdk) :
    NextReads (next sdk) (remaining sdk) (Valid sdk) := by
  intro ptr endp live
  rcases live with ⟨sameSlot,ordered,cell,which,last⟩
  have hcell := read_cell sdk ptr.slot cell which
  have hle : ptr.offset≤endp.offset := ordered
  have hend : endp.offset≤alloc.vec.Vec.len cell.bytes := by
    change endp.offset.val≤cell.bytes.val.length
    omega
  by_cases equal : ptr.offset=endp.offset
  · refine ⟨ptr,endp,?_,⟨sameSlot,ordered,cell,which,last⟩,?_⟩
    · have empty : remaining sdk ptr endp=[] := by
        simp only [remaining,which]
        have hlen : ptr.offset.val=cell.bytes.val.length := by rw [equal]; exact last
        rw [hlen,List.drop_length]
      rw [empty]
      simp only [next,source_next,sameSlot,hle,hcell,hend,equal,massert,if_pos,
        bind_tc_ok,Aeneas.Std.uncurry,wrap,List.head?_nil]
    · have hlen : ptr.offset.val=cell.bytes.val.length := by rw [equal]; exact last
      simp only [remaining,which,hlen,List.drop_length,List.tail_nil]
  · have less : ptr.offset.val<cell.bytes.val.length := by
      have unequal : ptr.offset.val≠endp.offset.val := by
        intro h
        exact equal (UScalar.eq_of_val_eq h)
      omega
    obtain ⟨byte,hbyte,hvalue⟩ := WP.spec_imp_exists
      (alloc.vec.Vec.index_usize_spec cell.bytes ptr.offset less)
    have readByte : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice U8)
        cell.bytes ptr.offset=ok byte := by
      rw [alloc.vec.Vec.index_slice_index]
      exact hbyte
    obtain ⟨offset',hadd,hoffset⟩ := add_total ptr.offset (by
      have bound := cell.bytes.property
      omega)
    let ptr' : DataPointer := {ptr with offset:=offset'}
    refine ⟨ptr',endp,?_,?_,?_⟩
    · have head : (remaining sdk ptr endp).head?=some byte := by
        simp only [remaining,which,List.head?_drop]
        rw [List.getElem?_eq_getElem less,←hvalue]
      rw [head]
      simp only [next,source_next,sameSlot,hle,hcell,hend,massert,if_pos,
        if_neg equal,readByte,hadd,bind_tc_ok,Aeneas.Std.uncurry,wrap,ptr']
    · refine ⟨sameSlot,?_,cell,which,last⟩
      change offset'.val≤endp.offset.val
      omega
    · simp only [remaining,ptr',which,List.tail_drop,hoffset]

/-- TOTAL constructor, retaining the concrete cell and all SDK state. -/
theorem begin_total (sdk : OwnedSdk) (slot : Usize) (cell : OwnedDataCell)
    (which : sdk.data_cells.val[slot.val]?=some cell) :
    ∃ iter, source_begin sdk slot=ok iter ∧
      Valid sdk iter.ptr iter.end_or_len ∧
      remaining sdk iter.ptr iter.end_or_len=cell.bytes.val := by
  have hcell := read_cell sdk slot cell which
  let iter : SourceIterator :=
    ⟨⟨slot,0#usize⟩,⟨slot,alloc.vec.Vec.len cell.bytes⟩⟩
  refine ⟨iter,?_,?_,?_⟩
  · simp only [source_begin,hcell,bind_tc_ok]
    rfl
  · refine ⟨rfl,?_,cell,which,?_⟩
    · change (0:Nat)≤cell.bytes.val.length
      omega
    · rfl
  · simp only [remaining,iter,which,UScalar.val_ofNat,List.drop_zero]

/-- Enclosing checkpoint guard with the actual extracted any loop, exact
predicate and concrete emitted SDK constructor/next installed. Only the
reached account-row correspondence remains; no iterator/scan/byte/cursor
success or native-step semantic premise remains in this reference theorem. -/
theorem source_guard_eq_owned {A : Type} (sdk : OwnedSdk) (slot : Usize)
    (cell : OwnedDataCell) (which : sdk.data_cells.val[slot.val]?=some cell)
    (reject resume : Result A) :
    (do let iter ← source_begin sdk slot
        let (hit,_) ← sourceAny (next sdk) nonzeroPredicate (wrap iter) ()
        if hit then reject else resume) =
    (do let hit ← AspisS2OwnedStage1.owned_checkpoint_nonzero cell.bytes
        if hit then reject else resume) := by
  obtain ⟨iter,hbegin,live,view⟩ := begin_total sdk slot cell which
  obtain ⟨iterOut,hrun⟩ := sourceAny_total (next sdk) (remaining sdk) (Valid sdk)
    (next_reads sdk) (wrap iter) live
  have viewed : remaining sdk (wrap iter).ptr (wrap iter).end_or_len=cell.bytes.val := view
  rw [hbegin,bind_tc_ok]
  simp only [Aeneas.Std.uncurry]
  rw [hrun,viewed,AspisS2OwnedStage1.CheckpointGuardTransport.owned_eq_std]
  rfl

#print axioms next_reads
#print axioms begin_total
#print axioms source_guard_eq_owned
end AspisS2SdkIterator
