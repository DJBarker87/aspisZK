import S2OwnedSourceInstallationV1
import S2CheckpointGuardTransportV1
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace AspisS2OwnedStage1.SourceInstallation

/-- Composition of the concrete emitted owned scan and installed owned tail.
This names the reference at the checkpoint-borrow cut. It does not assert the
unproved SDK wrapper/owned reference correspondence. The ordered IO children
are evaluated only after the scan accepts, at their original tail positions. -/
def afterCheckpointBorrow (ops : Ops) (verifierOps : AspisR1CurrentCaller.Ops)
    (checkpoint : alloc.vec.Vec U8) (data : Slice U8) :
    Result (core.result.Result Unit solana_program_error.ProgramError × Slice U8) := do
  let nonzero ← owned_checkpoint_nonzero checkpoint
  if nonzero then
    ok (.Err solana_program_error.ProgramError.AccountAlreadyInitialized,
      alloc.vec.Vec.deref checkpoint)
  else owned_stage1_tail (install ops verifierOps) (alloc.vec.Vec.deref checkpoint) data

/-- Reject branch, complete Result and unchanged bytes. No public/proof read,
decoder, verifier, or checkpoint write is evaluated on this branch. -/
theorem nonzero_reject (ops : Ops) (verifierOps : AspisR1CurrentCaller.Ops)
    (checkpoint : alloc.vec.Vec U8) (data : Slice U8)
    (h : CheckpointGuardTransport.stdAny checkpoint.val = true) :
    afterCheckpointBorrow ops verifierOps checkpoint data =
      ok (.Err solana_program_error.ProgramError.AccountAlreadyInitialized,
        alloc.vec.Vec.deref checkpoint) := by
  unfold afterCheckpointBorrow
  rw [CheckpointGuardTransport.owned_eq_std, h]
  rfl

/-- ACCEPTED-ONLY enclosing reference theorem. The zero-buffer and successful
scan premises are removed: both follow from the same guarded execution. The
actual SDK read/borrow interpretation is still explicitly uninstantiated. -/
theorem guarded_current_first (ops : Ops) (verifierOps : AspisR1CurrentCaller.Ops)
    (checkpoint : alloc.vec.Vec U8) (data checkpointOut : Slice U8)
    (h : afterCheckpointBorrow ops verifierOps checkpoint data=ok (.Ok (),checkpointOut)) :
    (∀ byte ∈ checkpoint.val, byte = 0#u8) ∧
    ∃ (publicData proofData : alloc.vec.Vec U8)
      (statement : AspisR1TerminalDecoder.PublicBinding.Statement)
      (selected : Slice U8) (splitByte : U8) (k : Usize) (cp : alloc.vec.Vec U8),
      ops.op11=ok (.Ok publicData) ∧ ops.op12=ok (.Ok proofData) ∧
      AspisR1PublicPreparation.S6DecoderScopedReuseV1.decodeActual
        (alloc.vec.Vec.deref publicData)=ok (.Ok statement) ∧
      alloc.vec.Vec.index (core.slice.index.SliceIndexRangeUsizeSlice U8) proofData
        {start:=688#usize,«end»:=58295#usize}=ok selected ∧
      Slice.index_usize data 1#usize=ok splitByte ∧
      lift (UScalar.cast .Usize splitByte)=ok k ∧
      AspisR1CurrentCaller.FirstComposition.firstCurrent
        solana_program_error.ProgramError.InvalidAccountData verifierOps
        (currentDigest (SolanaDigest.Insts.Aspis_coreDigestDigest32 (install ops verifierOps)))
        (fun e => ops.op10 (freshError e)) (alloc.vec.Vec.deref publicData) selected k=ok (.Ok cp) ∧
      core.slice.Slice.copy_from_slice core.marker.CopyU8 (alloc.vec.Vec.deref checkpoint)
        (alloc.vec.Vec.deref cp)=ok checkpointOut := by
  unfold afterCheckpointBorrow at h
  rw [CheckpointGuardTransport.owned_eq_std] at h
  cases hs : CheckpointGuardTransport.stdAny checkpoint.val with
  | true => simp only [hs,bind_tc_ok,Bool.true_eq,if_true] at h; cases h
  | false =>
    simp only [hs,bind_tc_ok,Bool.false_eq_true,if_false] at h
    exact ⟨(CheckpointGuardTransport.stdAny_false checkpoint.val).mp hs,
      tail_current_first ops verifierOps (alloc.vec.Vec.deref checkpoint) data checkpointOut h⟩

#print axioms nonzero_reject
#print axioms guarded_current_first
end AspisS2OwnedStage1.SourceInstallation
