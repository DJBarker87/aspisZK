import RPz7_S2SdkCheckpointWriterV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisS2OwnedStage1.SdkReference.CheckpointWriter
open GuardFrame BorrowedBufferFrame

/-- Exact whole byte-vector heap effect of the reached writer. -/
theorem written_image (sdk : OwnedSdk) (slot : Usize) (old : OwnedDataCell)
    (back : OwnedDataCell → alloc.vec.Vec OwnedDataCell) (bytes : alloc.vec.Vec U8)
    (index : alloc.vec.Vec.index_mut (core.slice.index.SliceIndexUsizeSlice OwnedDataCell)
      sdk.data_cells slot=ok (old,back)) :
    buffers {sdk with data_cells:=back {old with bytes:=bytes}} =
      (buffers sdk).set slot.val bytes := by
  obtain ⟨_,_,setter⟩ := index_mut_success sdk slot old back index
  subst back
  simp only [buffers,alloc.vec.Vec.set,List.map_set]

theorem released_written_image (initial sdk out : OwnedSdk) (guards : LiveGuards)
    (slot : Usize) (old : OwnedDataCell)
    (back : OwnedDataCell → alloc.vec.Vec OwnedDataCell) (bytes : alloc.vec.Vec U8)
    (index : alloc.vec.Vec.index_mut (core.slice.index.SliceIndexUsizeSlice OwnedDataCell)
      sdk.data_cells slot=ok (old,back))
    (release : owned_release_guards {sdk with data_cells:=back {old with bytes:=bytes}}
      guards=ok out)
    (prefixFrame : buffers sdk=buffers initial) :
    buffers out=(buffers initial).set slot.val bytes := by
  rw [ErrorBufferFrame.release_buffers _ out guards release,
    written_image sdk slot old back bytes index,prefixFrame]

#print axioms written_image
#print axioms released_written_image
end AspisS2OwnedStage1.SdkReference.CheckpointWriter
