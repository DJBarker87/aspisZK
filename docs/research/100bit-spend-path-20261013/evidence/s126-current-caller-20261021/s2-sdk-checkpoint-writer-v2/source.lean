import S2SdkFixedInputCallerV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
open Lean Elab Tactic Meta
namespace AspisS2OwnedStage1.SdkReference.CheckpointWriter
open GuardFrame BorrowedBufferFrame

/-- The actual reached mutable index determines the complete setter. The bytes
written by stage1 can be read back at that same slot, without a range premise. -/
theorem written_bytes (sdk : OwnedSdk) (slot : Usize) (old : OwnedDataCell)
    (back : OwnedDataCell → alloc.vec.Vec OwnedDataCell) (bytes : alloc.vec.Vec U8)
    (index : alloc.vec.Vec.index_mut (core.slice.index.SliceIndexUsizeSlice OwnedDataCell)
      sdk.data_cells slot=ok (old,back)) :
    readBytes {sdk with data_cells:=back {old with bytes:=bytes}} slot=ok bytes := by
  obtain ⟨valid,_,setter⟩ := index_mut_success sdk slot old back index
  subst back
  simp only [readBytes,alloc.vec.Vec.index_slice_index,alloc.vec.Vec.index_usize,
    alloc.vec.Vec.set]
  change (do
    let cell ← match (sdk.data_cells.val.set slot.val {old with bytes:=bytes})[slot.val]? with
      | none => Result.fail Error.arrayOutOfBounds
      | some cell => Result.ok cell
    Result.ok cell.bytes)=Result.ok bytes
  rw [List.getElem?_set_self valid]
  rfl

/-- The same bytes survive the complete actual guard-release finalizer,
including all reached arithmetic and mutable-index effects. -/
theorem released_written_bytes (sdk out : OwnedSdk) (guards : LiveGuards)
    (slot : Usize) (old : OwnedDataCell)
    (back : OwnedDataCell → alloc.vec.Vec OwnedDataCell) (bytes : alloc.vec.Vec U8)
    (index : alloc.vec.Vec.index_mut (core.slice.index.SliceIndexUsizeSlice OwnedDataCell)
      sdk.data_cells slot=ok (old,back))
    (release : owned_release_guards {sdk with data_cells:=back {old with bytes:=bytes}}
      guards=ok out) : readBytes out slot=ok bytes := by
  rw [readBytes_eq _ out slot (ErrorBufferFrame.release_buffers _ out guards release)]
  exact written_bytes sdk slot old back bytes index

#print axioms written_bytes
#print axioms released_written_bytes
end AspisS2OwnedStage1.SdkReference.CheckpointWriter
