import S2SdkOwnedGuardBodyV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisS2OwnedStage1.SdkReference.ReadyAcquire

/-- Forward, rather than accepted-run, form of the actual checkpoint helper.
The successful source read and zero count are precisely reached native facts. -/
theorem checkpoint_success (sdk : OwnedSdk) (guards : LiveGuards)
    (slot : Usize) (cell : OwnedDataCell)
    (read : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice OwnedDataCell)
      sdk.data_cells slot=ok cell)
    (zero : cell.borrowed=0#isize) :
    owned_acquire_checkpoint sdk guards slot=ok (.Ok (),
      GuardRelease.counterUpdate sdk slot cell (-1)#isize,
      {guards with checkpoint:=some slot}) := by
  have valid := GuardAcquire.index_success_valid sdk.data_cells slot cell read
  obtain ⟨actual,hactual,hread,hmut⟩ := BorrowTotal.cell_operations_total sdk slot valid
  have equal : actual=cell := Result.ok.inj (hread.symm.trans read)
  cases equal
  simp [owned_acquire_checkpoint,read,zero,hmut,GuardRelease.counterUpdate]


/-- Actual shared acquisition constructs its successful full-state return
from the source counter guard; neither child success nor final SDK success
is assumed. The checked increment is derived at isize::MAX-1 as well. -/
theorem shared_success (sdk : OwnedSdk) (slot : Usize) (cell : OwnedDataCell)
    (read : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice OwnedDataCell)
      sdk.data_cells slot=ok cell)
    (allowed : shared_allowed cell.borrowed=ok true) :
    ∃ (next : Isize),
      next.val=cell.borrowed.val+1 ∧
      owned_acquire_shared sdk slot=ok (.Ok (),
        GuardRelease.counterUpdate sdk slot cell next) := by
  have valid := GuardAcquire.index_success_valid sdk.data_cells slot cell read
  obtain ⟨actual,hactual,hread,hmut⟩ := BorrowTotal.cell_operations_total sdk slot valid
  have equal : actual=cell := Result.ok.inj (hread.symm.trans read)
  cases equal
  obtain ⟨current,status,out,hcurrent,step,alternatives⟩ :=
    BorrowTotal.shared_acquire_total sdk slot valid
  have currentEq : current=cell := hcurrent.trans hactual.symm
  cases currentEq
  rcases alternatives with rejected | ⟨next,result,_,_,value,image⟩
  · exact False.elim (rejected.2.2 ((PrimitivesTotal.shared_allowed_true cell.borrowed).mp allowed))
  · refine ⟨next,value,?_⟩
    rw [result,image] at step
    exact step

#print axioms checkpoint_success
#print axioms shared_success
end AspisS2OwnedStage1.SdkReference.ReadyAcquire
