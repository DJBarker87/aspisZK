import S126SdkAccountImageExportV1
import S2SdkErrorBufferJoinV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisS2OwnedStage1.SdkReference.ReferenceFirstReuse
open BorrowedBufferFrame ProofGate.FixedLinked CheckpointWriter

/-- A single byte-vector observation suffices, retaining invalid-slot errors. -/
theorem read_from_observation (initial out : OwnedSdk) (slot : Usize)
    (same : (buffers out)[slot.val]?=(buffers initial)[slot.val]?) :
    readBytes out slot=readBytes initial slot := by
  simp only [buffers,List.getElem?_map] at same
  simp only [readBytes,alloc.vec.Vec.index_slice_index,alloc.vec.Vec.index_usize]
  cases a : out.data_cells.val[slot.val]? <;>
    cases b : initial.data_cells.val[slot.val]? <;>
    simp_all only [Option.map_none,Option.map_some,Option.some.injEq,
      bind_tc_ok,bind_tc_fail]
  all_goals cases same

/-- Both statuses of the COMPLETE installed reference preserve every input
slot other than the checkpoint slot. This derives the frame from the run;
it is not supplied as an independent whole-buffer assumption. -/
theorem returned_other_read (ops : Ops) (verifierOps : AspisR1CurrentCaller.Ops)
    (program : Array U8 32#usize) (initial out : OwnedSdk) (data : alloc.vec.Vec U8)
    (status : core.result.Result Unit solana_program_error.ProgramError)
    (checkpointAccount : OwnedAccount) (queried : Usize)
    (accountRead : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice OwnedAccount)
      initial.accounts 2#usize=ok checkpointAccount)
    (different : checkpointAccount.data_slot.val ≠ queried.val)
    (run : BorrowedReference.owned_stage1 (Installation.install ops verifierOps)
      program initial data=ok (status,out)) :
    readBytes out queried=readBytes initial queried := by
  cases status with
  | Err error =>
    exact readBytes_eq initial out queried
      (ErrorBufferJoin.borrowed_error_buffers (Installation.install ops verifierOps)
        program initial out data error run)
  | Ok returned =>
    cases returned
    obtain ⟨_,_,_,_,_,_,_,account,observed,_,_,_,_,_,_,_,_,image⟩ :=
      borrowed_stage1_fixed_image_first ops verifierOps program initial out data run
    have sameAccount : account=checkpointAccount := Result.ok.inj (observed.symm.trans accountRead)
    subst account
    apply read_from_observation
    rw [image,List.getElem?_set_ne different]

/-- A returned vector read identifies the corresponding complete buffer-list
cell. No arbitrary chosen snapshot or slot-validity premise is introduced. -/
theorem read_observation (sdk : OwnedSdk) (slot : Usize) (bytes : alloc.vec.Vec U8)
    (read : readBytes sdk slot=ok bytes) : (buffers sdk)[slot.val]?=some bytes := by
  unfold readBytes at read
  cases selected : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice OwnedDataCell)
      sdk.data_cells slot with
  | fail error => simp only [selected,bind_tc_fail] at read; cases read
  | div => simp only [selected,bind_tc_div] at read; cases read
  | ok cell =>
    simp only [selected,bind_tc_ok] at read
    cases read
    simp only [alloc.vec.Vec.index_slice_index,alloc.vec.Vec.index_usize] at selected
    cases actual : sdk.data_cells.val[slot.val]? with
    | none => cases selected
    | some original =>
      cases selected
      simp only [buffers,List.getElem?_map,actual,Option.map_some]

/-- Restore ONLY the original checkpoint vector after either ordinary result
of the fixed-initial complete reference. The resulting entire buffer heap is
exactly the initial heap. This justifies reference-first paired execution
without cloning the58295-byte proof or relying on any post-native byte frame.
Actual Rust moves/clone, native source ports/runtime/oracle and native output
frame remain separate concrete source obligations. -/
theorem restore_checkpoint_buffers (ops : Ops) (verifierOps : AspisR1CurrentCaller.Ops)
    (program : Array U8 32#usize) (initial out : OwnedSdk) (data : alloc.vec.Vec U8)
    (status : core.result.Result Unit solana_program_error.ProgramError)
    (checkpointAccount : OwnedAccount) (original : alloc.vec.Vec U8)
    (accountRead : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice OwnedAccount)
      initial.accounts 2#usize=ok checkpointAccount)
    (originalRead : readBytes initial checkpointAccount.data_slot=ok original)
    (run : BorrowedReference.owned_stage1 (Installation.install ops verifierOps)
      program initial data=ok (status,out)) :
    (buffers out).set checkpointAccount.data_slot.val original=buffers initial := by
  have originalCell := read_observation initial checkpointAccount.data_slot original originalRead
  obtain ⟨valid,selected⟩ := List.getElem?_eq_some_iff.mp originalCell
  have reset : (buffers initial).set checkpointAccount.data_slot.val original=buffers initial := by
    rw [←selected]
    exact List.set_getElem_self valid
  cases status with
  | Err error =>
    rw [ErrorBufferJoin.borrowed_error_buffers (Installation.install ops verifierOps)
      program initial out data error run]
    exact reset
  | Ok returned =>
    cases returned
    obtain ⟨_,_,_,_,_,_,_,account,observed,_,_,_,_,_,_,_,_,image⟩ :=
      borrowed_stage1_fixed_image_first ops verifierOps program initial out data run
    have sameAccount : account=checkpointAccount := Result.ok.inj (observed.symm.trans accountRead)
    subst account
    rw [image,List.set_set]
    exact reset

#print axioms read_from_observation
#print axioms returned_other_read
#print axioms read_observation
#print axioms restore_checkpoint_buffers
end AspisS2OwnedStage1.SdkReference.ReferenceFirstReuse
