import S2SdkBorrowedReferenceV1
import S2SdkOwnedGuardFrameV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisS2OwnedStage1.SdkReference.BorrowedBufferFrame
open GuardRelease GuardAcquire

/-- Complete byte-vector heap, including lengths and invalid-slot behaviour. -/
def buffers (sdk : OwnedSdk) : List (alloc.vec.Vec U8) :=
  sdk.data_cells.val.map OwnedDataCell.bytes

theorem counter_update_buffers (sdk : OwnedSdk) (slot : Usize)
    (cell : OwnedDataCell) (next : Isize)
    (valid : slot.val<sdk.data_cells.val.length)
    (actual : cell=sdk.data_cells.val[slot.val]) :
    buffers (counterUpdate sdk slot cell next)=buffers sdk := by
  subst cell
  simp only [buffers,counterUpdate,alloc.vec.Vec.set]
  rw [List.map_set]
  have mappedValid : slot.val<(sdk.data_cells.val.map OwnedDataCell.bytes).length := by simpa using valid
  have selected : (sdk.data_cells.val.map OwnedDataCell.bytes)[slot.val] =
      (sdk.data_cells.val[slot.val]).bytes := by simp
  rw [← selected]
  exact List.set_getElem_self mappedValid

/-- This is the emitted candidate helper, not a replacement contract. -/
theorem acquire_source_eq (sdk : OwnedSdk) (slot : Usize) :
    BorrowedReference.owned_acquire_shared sdk slot=owned_acquire_shared sdk slot := rfl

/-- Every ordinary acquisition return preserves every buffer, even on
AccountBorrowFailed and when the queried buffer aliases the acquired slot.
The reached source read supplies validity; callers add no range premise. -/
theorem acquire_buffers (sdk out : OwnedSdk) (slot : Usize)
    (result : core.result.Result Unit solana_program_error.ProgramError)
    (execution : BorrowedReference.owned_acquire_shared sdk slot=ok (result,out)) :
    buffers out=buffers sdk := by
  rw [acquire_source_eq] at execution
  have step := execution
  unfold owned_acquire_shared at step
  cases read : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice OwnedDataCell)
      sdk.data_cells slot with
  | fail error => simp only [read,bind_tc_fail] at step; cases step
  | div => simp only [read,bind_tc_div] at step; cases step
  | ok first =>
    have valid := index_success_valid sdk.data_cells slot first read
    obtain ⟨cell,reply,state,actual,run,alternatives⟩ :=
      BorrowTotal.shared_acquire_total sdk slot valid
    have equal := Prod.mk.inj (Result.ok.inj (run.symm.trans execution))
    rcases equal with ⟨replyEq,stateEq⟩
    subst reply
    subst state
    rcases alternatives with failed | success
    · rcases failed with ⟨_,rfl,_⟩; rfl
    · rcases success with ⟨next,_,_,_,_,rfl⟩
      exact counter_update_buffers sdk slot cell next valid actual

#print axioms counter_update_buffers
#print axioms acquire_source_eq
#print axioms acquire_buffers
end AspisS2OwnedStage1.SdkReference.BorrowedBufferFrame
