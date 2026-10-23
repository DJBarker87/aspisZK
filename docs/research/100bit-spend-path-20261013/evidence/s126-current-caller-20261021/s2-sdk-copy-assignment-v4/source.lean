import S2SdkCopyLoopTotalV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisS2OwnedStage1.SdkReference.CopyLoop

/-- Exact old post-child assignment, retaining ordinary errors and guards.
The complete parent fission gate connects this expression to both source sites. -/
def finishAssignment (sdk : OwnedSdk) (slot : Usize) (source : alloc.vec.Vec U8)
    (guards : LiveGuards) :
    Result ((core.result.Result Unit solana_program_error.ProgramError) × OwnedSdk × LiveGuards) := do
  let sourceLength := alloc.vec.Vec.len source
  let cell ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice OwnedDataCell) sdk.data_cells slot
  let targetLength := alloc.vec.Vec.len cell.bytes
  if sourceLength != targetLength then
    ok (core.result.Result.Err solana_program_error.ProgramError.InvalidAccountData,sdk,guards)
  else
    let (old,back) ← alloc.vec.Vec.index_mut
      (core.slice.index.SliceIndexUsizeSlice OwnedDataCell) sdk.data_cells slot
    ok (core.result.Result.Ok (),{sdk with data_cells:=back {old with bytes:=source}},guards)

def finishLoop (sdk : OwnedSdk) (slot : Usize) (source : alloc.vec.Vec U8)
    (guards : LiveGuards) :
    Result ((core.result.Result Unit solana_program_error.ProgramError) × OwnedSdk × LiveGuards) := do
  let (status,heap) ← copy_in_place sdk slot (alloc.vec.Vec.deref source)
  ok (status,heap,guards)

/-- All-outcome equality, including invalid slots, wrong lengths, failure and
divergence. Valid indexing and successful loop traversal are derived internally. -/
theorem finish_eq (sdk : OwnedSdk) (slot : Usize) (source : alloc.vec.Vec U8)
    (guards : LiveGuards) : finishLoop sdk slot source guards=finishAssignment sdk slot source guards := by
  cases read : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice OwnedDataCell)
      sdk.data_cells slot with
  | fail error =>
    simp only [finishLoop,copy_in_place,finishAssignment,alloc.vec.Vec.deref,read,bind_tc_fail]
  | div =>
    simp only [finishLoop,copy_in_place,finishAssignment,alloc.vec.Vec.deref,read,bind_tc_div]
  | ok selected =>
    have valid := GuardAcquire.index_success_valid sdk.data_cells slot selected read
    obtain ⟨cell,actual,actualRead,actualMut⟩ := BorrowTotal.cell_operations_total sdk slot valid
    have selectedEq : selected=cell := Result.ok.inj (read.symm.trans actualRead)
    subst selected
    obtain ⟨loopCell,loopActual,loopTotal⟩ := copy_in_place_total sdk slot
      (alloc.vec.Vec.deref source) valid
    have cellEq : loopCell=cell := loopActual.trans actual.symm
    rw [cellEq] at loopTotal
    simp only [alloc.vec.Vec.deref] at loopTotal
    by_cases sameLength : cell.bytes.val.length=source.val.length
    · have sizeEq : alloc.vec.Vec.len source=alloc.vec.Vec.len cell.bytes :=
        UScalar.eq_of_val_eq sameLength.symm
      simp only [finishLoop,alloc.vec.Vec.deref,loopTotal,if_pos sameLength,bind_tc_ok,Aeneas.Std.uncurry,
        finishAssignment,actualRead,sizeEq,bne_self_eq_false,Bool.false_eq_true,if_false,
        actualMut,replaceBytes]
      rfl
    · have sizeNe : alloc.vec.Vec.len source≠alloc.vec.Vec.len cell.bytes := by
        intro equal
        exact sameLength (congrArg (fun value : Usize => value.val) equal).symm
      have mismatch : (alloc.vec.Vec.len source != alloc.vec.Vec.len cell.bytes)=true := bne_iff_ne.mpr sizeNe
      simp only [finishLoop,alloc.vec.Vec.deref,loopTotal,if_neg sameLength,bind_tc_ok,Aeneas.Std.uncurry,
        finishAssignment,actualRead,mismatch,if_true]

#print axioms finish_eq
end AspisS2OwnedStage1.SdkReference.CopyLoop
