import Port6CK_Checkpoint
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port6CK_Ordered
open Aeneas Aeneas.Std Result VTop_Stages
open CheckpointBytes3Namespaces CheckpointBytes5Effect CheckpointBytes5Inputs
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open Port6CK_Semantic (Unwrap)

def stage (reserved : Bool) (unwrap : Unwrap)
    (p : CheckpointBytes5Writer.Prepared) (a : CheckpointBytes5Writer.Accumulator)
    (proof pub : Slice U8) : Code (core.result.Result (verifier.Prepared × verifier.Accumulator) AspisR1Stage2.verifier.Error) := do
  let ck ← CheckpointBytes5Writer.writer p a proof pub
  CheckpointBytes5Resume.program (Port6CK_Ops.ops reserved unwrap) ck proof pub .S2

theorem combined_run (reserved : Bool) (unwrap : Unwrap)
    (unwrap_ok : ∀ N b, unwrap N (.Ok b)=ok b) {H : Type}
    (D : aspis_core.digest.Digest32 H) (hash : H)
    (p : verifier.Prepared) (a : verifier.Accumulator) (proof pub : Slice U8)
    (saved : alloc.vec.Vec U8) (p1 : verifier.Prepared) (a1 : verifier.Accumulator)
    (wrote : Port3_CheckpointInstall.writer D p a proof pub hash=ok saved)
    (resumed : Port6CK_Reader.reader reserved unwrap D (VTop_Checkpoint.checkpointSlice saved) proof pub .S2 hash=ok (.Ok (p1,a1)))
    (before : Log) :
    ∃ after,
      run (VTop_Checkpoint.digest D) hash (stage reserved unwrap (toPrepared p) (toAccumulator a) proof pub) before=ok (.Ok (p1,a1),after) ∧
      run (VTop_Checkpoint.digest D) hash (CheckpointBytes5Join.stage reserved (toPrepared p) (toAccumulator a) proof pub) before=ok (.Ok (p1,a1),after) := by
  obtain ⟨middle,writerRun⟩ := Port3_CheckpointInstall.writer_run D p a proof pub hash saved wrote before
  obtain ⟨after,current,retained⟩ := Port6CK_Reader.runs reserved unwrap unwrap_ok D hash
    (VTop_Checkpoint.checkpointSlice saved) proof pub p1 a1 middle resumed
  refine ⟨after,?_,?_⟩
  · simp only [stage,run_bind,writerRun,bind_tc_ok,Aeneas.Std.uncurry]
    exact current
  · simp only [CheckpointBytes5Join.stage,run_bind,writerRun,bind_tc_ok,Aeneas.Std.uncurry]
    exact retained

#print axioms combined_run
end AspisR1.Port6CK_Ordered
end
