import S2SdkFixedInputCallerV1
import S2SdkCheckpointSizeTotalV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisS2OwnedStage1.SdkReference.CheckpointWriter
open ProofGate.FixedLinked

private theorem len_bind_success {A B : Type} (m : Result A) (f : A → Result B) (out : B)
    (h : (do let a ← m; f a)=ok out) : ∃ a,m=ok a ∧ f a=ok out := by
  cases m with
  | ok a => exact ⟨a,rfl,h⟩
  | fail e => simp only [bind_tc_fail] at h;cases h
  | div => simp only [bind_tc_div] at h;cases h

/-- Successful actual length read exposes its actual input bytes, without an
independent slot-validity, borrow-success or length premise. -/
theorem data_len_bytes (sdk : OwnedSdk) (slot : Usize) (n : Usize)
    (h : owned_data_len sdk slot=ok (.Ok n)) :
    ∃ bytes : alloc.vec.Vec U8,
      BorrowedBufferFrame.readBytes sdk slot=ok bytes ∧ alloc.vec.Vec.len bytes=n := by
  unfold owned_data_len at h
  obtain ⟨cell,read,h⟩ := len_bind_success _ _ _ h
  obtain ⟨allowed,_,h⟩ := len_bind_success _ _ _ h
  cases allowed
  · cases h
  · cases h
    exact ⟨cell.bytes,by simp only [BorrowedBufferFrame.readBytes,read,bind_tc_ok],rfl⟩

/-- A reached caller's original checkpoint size, same-byte reread and actual
successful output length check imply1768. All arithmetic reuses the existing
TOTAL S2 checkpoint-size theorem; the enclosing source supplies these facts. -/
theorem checkpoint_length_from_calls (initial : OwnedSdk) (account : OwnedAccount)
    (beforeWrite checkpoint : alloc.vec.Vec U8) (header size : Usize)
    (accountRead : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice OwnedAccount)
      initial.accounts 2#usize=ok account)
    (origin : inputBytes initial 2#usize=ok (alloc.vec.Vec.deref beforeWrite))
    (headerRead : owned_data_len initial account.data_slot=ok (.Ok header))
    (sizeRead : aspis_r1_cost_probe.verifier.checkpoint_size .S2=ok size)
    (sameHeader : header=size)
    (sameLength : alloc.vec.Vec.len checkpoint=alloc.vec.Vec.len beforeWrite) :
    checkpoint.val.length=1768 := by
  obtain ⟨original,read,length⟩ := data_len_bytes initial account.data_slot header headerRead
  have input : inputBytes initial 2#usize=ok (alloc.vec.Vec.deref original) := by
    simp only [inputBytes,accountRead,read,bind_tc_ok]
  have views := Result.ok.inj (input.symm.trans origin)
  have byteLengths := congrArg (fun s : Slice U8 => s.val.length) views
  simp only [FrameOperationsTotal.deref_val] at byteLengths
  have sizeEq := Result.ok.inj (sizeRead.symm.trans CheckpointSizeTotal.checkpoint_size_S2)
  have headerValue := congrArg UScalar.val (sameHeader.trans sizeEq)
  have originalValue := congrArg UScalar.val length
  have checkpointValue := congrArg UScalar.val sameLength
  change header.val=1768 at headerValue
  change original.val.length=header.val at originalValue
  change checkpoint.val.length=beforeWrite.val.length at checkpointValue
  omega

#print axioms data_len_bytes
#print axioms checkpoint_length_from_calls
end AspisS2OwnedStage1.SdkReference.CheckpointWriter
