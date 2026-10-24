import Port4A_ReaderInstall
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port4A_CheckpointRows
open Aeneas Aeneas.Std Result VTop_Stages
open CheckpointBytes5Effect CheckpointBytes5Inputs Port3_CheckpointInstall
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open MultiproofConeCanonical OraclePortCompactDraft

theorem combined_run (base : Ops) (reserved : Bool) {H : Type}
    (D : aspis_core.digest.Digest32 H) (hash : H)
    (wp : verifier.Prepared) (wa : verifier.Accumulator)
    (proof pub : Slice U8) (saved : alloc.vec.Vec U8)
    (p : verifier.Prepared) (a : verifier.Accumulator)
    (wrote : (Port4A_ReaderInstall.install (Port3_CheckpointInstall.install base reserved) reserved).op8 D wp wa proof pub hash = ok saved)
    (resumed : (Port4A_ReaderInstall.install (Port3_CheckpointInstall.install base reserved) reserved).op18 D (VTop_Checkpoint.checkpointSlice saved)
      proof pub .S2 hash = ok (.Ok (p,a))) (before : Log) :
    ∃ after, run (VTop_Checkpoint.digest D) hash
      (CheckpointBytes5Join.stage reserved (CheckpointBytes3Namespaces.toPrepared wp)
        (CheckpointBytes3Namespaces.toAccumulator wa) proof pub) before = ok (.Ok (p,a),after) := by
  obtain ⟨middle,writerRun⟩ := writer_run D wp wa proof pub hash saved wrote before
  have readerSource := Port4A_ReaderInstall.accepted_source _ reserved D hash
    (VTop_Checkpoint.checkpointSlice saved) proof pub .S2 p a resumed
  have readerErase : erase (VTop_Checkpoint.digest D) hash
      (CheckpointBytes5Resume.program (CheckpointBytes4Ops.ops reserved)
        (VTop_Checkpoint.checkpointSlice saved) proof pub .S2) = ok (.Ok (p,a)) := by
    rw [CheckpointBytes5Resume.source]
    exact readerSource
  obtain ⟨after,readerRun⟩ := erase_success_run _ _ _ _ readerErase middle
  refine ⟨after,?_⟩
  simp only [CheckpointBytes5Join.stage,run_bind,writerRun,bind_tc_ok,Aeneas.Std.uncurry]
  exact readerRun

/-- All returned fields and all six reads, with the same source slices and
actual returned checkpoint; no independent checkpoint execution is assumed. -/
theorem fields_and_reads (base : Ops) (reserved : Bool) {Hash : Type}
    (D : aspis_core.digest.Digest32 Hash) (hash : Hash) (H : Bytes → State)
    (wp : verifier.Prepared) (wa : verifier.Accumulator)
    (proof pub : Slice U8) (stored publicBytes : Bytes)
    (pm : OraclePortCheckpointAbiC5.Prepared)
    (am : QueryAccumulator.State OraclePortCheckpointAbiC5.K OraclePortCheckpointAbiC5.E)
    (caller : CheckpointBytes5Join.S2S10CallerBinding (VTop_Checkpoint.digest D)
      hash H proof pub stored publicBytes)
    (provenance : CheckpointBytes5Join.S1S7S8StateProvenance
      (CheckpointBytes3Namespaces.toPrepared wp) (CheckpointBytes3Namespaces.toAccumulator wa) pm am)
    (saved : alloc.vec.Vec U8) (p : verifier.Prepared) (a : verifier.Accumulator)
    (wrote : (Port4A_ReaderInstall.install (Port3_CheckpointInstall.install base reserved) reserved).op8 D wp wa proof pub hash = ok saved)
    (resumed : (Port4A_ReaderInstall.install (Port3_CheckpointInstall.install base reserved) reserved).op18 D (VTop_Checkpoint.checkpointSlice saved)
      proof pub .S2 hash = ok (.Ok (p,a))) (before : Log) :
    ∃ after,
      run (VTop_Checkpoint.digest D) hash
        (CheckpointBytes5Join.stage reserved (CheckpointBytes3Namespaces.toPrepared wp)
          (CheckpointBytes3Namespaces.toAccumulator wa) proof pub) before = ok (.Ok (p,a),after) ∧
      CheckpointBytes4SavedFields.BodyMatches p a pm am ∧ a.next.val = am.next ∧
      reserved = true ∧ observe after = observe before ++
        CheckpointBytes5Join.six H stored publicBytes
          (OraclePortPhysicalFrameDraft.domain ++ OraclePortCheckpointAbiC5.body pm am
            (H stored) (H publicBytes)) := by
  obtain ⟨after,success⟩ := combined_run base reserved D hash wp wa proof pub saved p a wrote resumed before
  exact ⟨after,success,CheckpointBytes5Join.successful_fields_and_reads
    (VTop_Checkpoint.digest D) hash H reserved _ _ proof pub stored publicBytes pm am
    caller provenance p a before after success⟩


#print axioms combined_run
#print axioms fields_and_reads
end AspisR1.Port4A_CheckpointRows
end
