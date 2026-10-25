import Op5T_Install
import Port4B_Install
set_option autoImplicit false
noncomputable section
namespace AspisR1.Op5T_Concrete
open Aeneas Aeneas.Std Result

/-- Both slots use the same fully fixed P6/native batch children. -/
def current (base : AspisR1CurrentCaller.Ops) : AspisR1CurrentCaller.Ops :=
  Op5T_Install.current base Port4B_Install.leaves

def stage (base : VTop_Stages.Ops) : VTop_Stages.Ops :=
  Op5T_Install.stage base Port4B_Install.leaves

/-- Full Result correspondence to the existing concrete native batch body.
No parsed wire, model queries, successful batch or equal-root premise. -/
theorem stage_source {Hash : Type} (D : VTop_Stages.aspis_core.digest.Digest32 Hash)
    (proof : Slice U8) (p : VTop_Stages.verifier.Prepared)
    (folded : Array U8 32#usize) (batch : Usize) (hash : Hash) :
    Op5T_Install.stageBatch Port4B_Install.leaves D proof p folded batch hash =
      Port4B_Install.batch D proof p folded batch hash := by
  unfold Op5T_Install.stageBatch Op5T_Install.mapResult Op5T_Install.body
    Port4B_Install.batch Port3_BatchStage.batch Port3_QueryInstall.result
    Port3_NativeBatchBody.verifier.candidate.batch_merkle
    VTop_Checkpoint.digest Op5T_Install.stageError Port3_CheckpointInstall.error
  rfl

/-- TX1 reads its own Prepared queries and roots. The only nominal transport
is digest and Error; it does not replace these inputs with model projections. -/
theorem current_source {Hash : Type} (D : AspisR1CurrentCaller.aspis_core.digest.Digest32 Hash)
    (proof : Slice U8) (p : AspisR1CurrentCaller.verifier.Prepared)
    (folded : Array U8 32#usize) (batch : Usize) (hash : Hash) :
    Op5T_Install.currentBatch Port4B_Install.leaves D proof p folded batch hash =
      Op5T_Install.mapResult Op5T_Install.currentError
        (Op5T_Install.body Port4B_Install.leaves
          {coremarkerCopyInst := D.coremarkerCopyInst, digest := D.digest}
          proof p.queries p.roots folded batch hash) := rfl

#print axioms stage_source
#print axioms current_source
end AspisR1.Op5T_Concrete
end
