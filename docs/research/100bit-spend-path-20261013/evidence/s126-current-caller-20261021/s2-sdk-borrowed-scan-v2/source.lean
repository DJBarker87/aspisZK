import S2SdkBorrowedReferenceV1
import S2SdkSourceScanV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisS2OwnedStage1.SdkReference.BorrowedScan

theorem step_eq (bytes : alloc.vec.Vec U8) (offset : Usize) :
    BorrowedReference.owned_checkpoint_nonzero_loop.body (alloc.vec.Vec.deref bytes) offset =
      owned_checkpoint_nonzero_loop.body bytes offset := by
  simp only [BorrowedReference.owned_checkpoint_nonzero_loop.body,
    owned_checkpoint_nonzero_loop.body,alloc.vec.Vec.index_slice_index,
    alloc.vec.Vec.index_usize,alloc.vec.Vec.len,alloc.vec.Vec.deref,
    Slice.len,Slice.index_usize]
  rfl

theorem scan_eq (bytes : alloc.vec.Vec U8) :
    BorrowedReference.owned_checkpoint_nonzero (alloc.vec.Vec.deref bytes)=
      owned_checkpoint_nonzero bytes := by
  unfold BorrowedReference.owned_checkpoint_nonzero owned_checkpoint_nonzero
  unfold BorrowedReference.owned_checkpoint_nonzero_loop owned_checkpoint_nonzero_loop
  simp only [step_eq]
  rfl

/-- Complete emitted borrowed scan subcomputation, including invalid slots. -/
def borrowedScan (sdk : OwnedSdk) (slot : Usize) : Result Bool := do
  let cell ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice OwnedDataCell)
    sdk.data_cells slot
  BorrowedReference.owned_checkpoint_nonzero (alloc.vec.Vec.deref cell.bytes)

theorem borrowedScan_eq_snapshotScan (sdk : OwnedSdk) (slot : Usize) :
    borrowedScan sdk slot=AspisS2SdkIterator.snapshotScan sdk slot := by
  unfold borrowedScan AspisS2SdkIterator.snapshotScan
  congr 1
  funext cell
  rw [PrimitivesTotal.bytes_clone_total]
  simp only [bind_tc_ok,scan_eq]

/-- TOTAL source scanner equality; no all-zero, scan-success or slot premise. -/
theorem borrowedScan_eq_sourceScan (sdk : OwnedSdk) (slot : Usize) :
    borrowedScan sdk slot=AspisS2SdkIterator.sourceScan sdk slot := by
  rw [borrowedScan_eq_snapshotScan,AspisS2SdkIterator.snapshotScan_eq_sourceScan]

#print axioms step_eq
#print axioms scan_eq
#print axioms borrowedScan_eq_sourceScan
end AspisS2OwnedStage1.SdkReference.BorrowedScan
