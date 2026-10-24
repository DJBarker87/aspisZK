import S2SdkSourceIteratorTotalV1
import S2SdkOwnedGuardAcquireV1
import S2SdkOwnedScanTotalV1
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace AspisS2SdkIterator
open AspisS2OwnedStage1.SdkReference
open AspisS2StdAnySource

/-- Literal read/clone/scan subcomputation of the complete emitted parent. -/
def snapshotScan (sdk : OwnedSdk) (slot : Usize) : Result Bool := do
  let cell ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice OwnedDataCell)
    sdk.data_cells slot
  let bytes ← alloc.vec.CloneVec.clone core.clone.CloneU8 cell.bytes
  owned_checkpoint_nonzero bytes

/-- Actual extracted std any body/predicate with the native-checked owned SDK
constructor and next operations installed. The full SDK heap is retained. -/
def sourceScan (sdk : OwnedSdk) (slot : Usize) : Result Bool := do
  let iter ← source_begin sdk slot
  let (hit,_) ← sourceAny (next sdk) nonzeroPredicate (wrap iter) ()
  ok hit

/-- TOTAL equality of complete scan subcomputations, including invalid slots.
No iterator, constructor, byte-copy, scan-success or all-zero premise remains. -/
theorem snapshotScan_eq_sourceScan (sdk : OwnedSdk) (slot : Usize) :
    snapshotScan sdk slot=sourceScan sdk slot := by
  cases read : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice OwnedDataCell)
      sdk.data_cells slot with
  | fail error =>
    simp only [snapshotScan,sourceScan,source_begin,read,bind_tc_fail]
  | div =>
    simp only [snapshotScan,sourceScan,source_begin,read,bind_tc_div]
  | ok cell =>
    have valid := GuardAcquire.index_success_valid sdk.data_cells slot cell read
    obtain ⟨actual,hactual,hread,_⟩ := BorrowTotal.cell_operations_total sdk slot valid
    have equal : actual=cell := Result.ok.inj (hread.symm.trans read)
    have which : sdk.data_cells.val[slot.val]?=some cell := by
      rw [List.getElem?_eq_getElem valid,←hactual,equal]
    obtain ⟨iter,hbegin,live,view⟩ := begin_total sdk slot cell which
    obtain ⟨iterOut,hrun⟩ := sourceAny_total (next sdk) (remaining sdk) (Valid sdk)
      (next_reads sdk) (wrap iter) live
    have viewed : remaining sdk (wrap iter).ptr (wrap iter).end_or_len=cell.bytes.val := view
    rw [sourceScan,hbegin,bind_tc_ok,hrun]
    simp only [Aeneas.Std.uncurry,bind_tc_ok,viewed]
    rw [snapshotScan,read,bind_tc_ok,PrimitivesTotal.bytes_clone_total,bind_tc_ok]
    rw [ScanTotal.scan_eq,AspisS2OwnedStage1.CheckpointGuardTransport.owned_eq_std]

#print axioms snapshotScan_eq_sourceScan
end AspisS2SdkIterator
