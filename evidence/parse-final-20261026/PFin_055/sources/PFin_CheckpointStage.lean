import F3Q_CheckpointStage
set_option autoImplicit false
noncomputable section
namespace AspisR1.PFin_CheckpointStage
open Aeneas Aeneas.Std Result AspisR1Stage2 CheckpointBytes5Effect CheckpointBytes3Namespaces

theorem erased {Hash : Type} (D : VTop_Stages.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (reserved : Bool) (p : verifier.Prepared) (a : verifier.Accumulator) (proof pub : Slice U8)
    (saved : alloc.vec.Vec U8) (p2 : verifier.Prepared) (a2 : verifier.Accumulator)
    (writer : Port3_CheckpointInstall.writer D p a proof pub hash=ok saved)
    (reader : verifier.resumeWithOps (CheckpointBytes4Ops.ops reserved)
      (VTop_Checkpoint.digest D) saved.deref proof pub .S2 hash=ok (.Ok (p2,a2))) :
    erase (VTop_Checkpoint.digest D) hash
      (CheckpointBytes5Join.stage reserved (toPrepared p) (toAccumulator a) proof pub)=ok (.Ok (p2,a2)) := by
  have wrote := F3N_WriterReturned.erased D hash p a proof pub saved writer
  simp only [CheckpointBytes5Join.stage,erase_bind,wrote,bind_tc_ok,CheckpointBytes5Resume.source]
  exact reader

#print axioms erased
end AspisR1.PFin_CheckpointStage
end
