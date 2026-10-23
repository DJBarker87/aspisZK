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

/-- Literal byte read used at decoder/verifier entry, retaining bounds failure. -/
def readBytes (sdk : OwnedSdk) (slot : Usize) : Result (alloc.vec.Vec U8) := do
  let cell ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice OwnedDataCell)
    sdk.data_cells slot
  ok cell.bytes

theorem readBytes_eq (before after : OwnedSdk) (slot : Usize)
    (same : buffers after=buffers before) :
    readBytes after slot=readBytes before slot := by
  have observed := congrArg (fun xs : List (alloc.vec.Vec U8) => xs[slot.val]?) same
  simp only [buffers,List.getElem?_map] at observed
  simp only [readBytes,alloc.vec.Vec.index_slice_index,alloc.vec.Vec.index_usize]
  cases a : after.data_cells.val[slot.val]? <;>
    cases b : before.data_cells.val[slot.val]? <;>
    simp_all only [Option.map_none,Option.map_some,Option.some.injEq,
      bind_tc_ok,bind_tc_fail]
  all_goals cases observed

theorem acquire_preserves_read (sdk out : OwnedSdk) (acquired queried : Usize)
    (result : core.result.Result Unit solana_program_error.ProgramError)
    (execution : BorrowedReference.owned_acquire_shared sdk acquired=ok (result,out)) :
    readBytes out queried=readBytes sdk queried :=
  readBytes_eq sdk out queried (acquire_buffers sdk out acquired result execution)

/-- The stage-1 seam in continuation form: after a previously reached public
read, inserting the candidate's public re-read after proof acquisition changes
neither any continuation result nor the returned SDK passed to it. Acquisition
failure/divergence and every ordinary error value remain in the computation. -/
theorem acquire_reborrow_eq {T : Type} (sdk : OwnedSdk) (acquired queried : Usize)
    (prior : OwnedDataCell)
    (reached : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice OwnedDataCell)
      sdk.data_cells queried=ok prior)
    (k : core.result.Result Unit solana_program_error.ProgramError →
      OwnedSdk → alloc.vec.Vec U8 → Result T) :
    (do
      let (result,out) ← BorrowedReference.owned_acquire_shared sdk acquired
      let cell ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice OwnedDataCell)
        out.data_cells queried
      k result out cell.bytes) =
    (do
      let (result,out) ← owned_acquire_shared sdk acquired
      k result out prior.bytes) := by
  rw [acquire_source_eq]
  cases execution : owned_acquire_shared sdk acquired with
  | fail error => simp only [bind_tc_fail]
  | div => simp only [bind_tc_div]
  | ok pair =>
    rcases pair with ⟨result,out⟩
    have preserved := acquire_preserves_read sdk out acquired queried result
      ((acquire_source_eq sdk acquired).trans execution)
    have original : readBytes sdk queried=ok prior.bytes := by
      simp only [readBytes,reached,bind_tc_ok]
    have read := preserved.trans original
    simp only [bind_tc_ok]
    unfold readBytes at read
    cases fetched : alloc.vec.Vec.index
        (core.slice.index.SliceIndexUsizeSlice OwnedDataCell) out.data_cells queried with
    | fail error => simp only [fetched,bind_tc_fail] at read; cases read
    | div => simp only [fetched,bind_tc_div] at read; cases read
    | ok cell =>
      simp only [fetched,bind_tc_ok] at read ⊢
      rw [Result.ok.inj read]
      rfl

#print axioms acquire_reborrow_eq
#print axioms readBytes_eq
#print axioms acquire_preserves_read
#print axioms counter_update_buffers
#print axioms acquire_source_eq
#print axioms acquire_buffers
end AspisS2OwnedStage1.SdkReference.BorrowedBufferFrame
