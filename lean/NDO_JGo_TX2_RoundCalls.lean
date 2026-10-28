import NDO_JGo_TX2_Round0
import NDO_JGo_TX2_Round1
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGo_TX2_RoundCalls
open Aeneas Aeneas.Std Result AspisR1Stage2.Stage2Finish

theorem first (seed : FinishOps FIo_Install.W) :
    Port4D_Round.round (Port3_FinishStage.release (FIo_Install.finishOps (.Ok ()) seed))
      (JFw_Frames.window 7527 224) JFq_Alpha0.scalar JFq_Claim.scalar 0#usize=
        ok (.Ok JGo_TX2_Horner0_6.after) := by
  classical
  have h := RowFinish_Control.round_value (FIo_Install.finishOps (.Ok ()) seed)
    (JFw_Frames.window 7527 224) JFq_Alpha0.scalar JFq_Claim.scalar 0#usize
    (JGo_TX2_Round0.values seed)
  change _=ok (if JGo_TX2_Round0.boundary=JGo_TX2_Round0.boundary
    then core.result.Result.Ok JGo_TX2_Horner0_6.after else core.result.Result.Err AspisR1Stage2.verifier.Error.Relation) at h
  rw [if_pos rfl] at h
  exact h
#print axioms first

theorem second (seed : FinishOps FIo_Install.W) :
    Port4D_Round.round (Port3_FinishStage.release (FIo_Install.finishOps (.Ok ()) seed))
      (JFw_Frames.window 7783 224) JFq_Alpha1.scalar JGo_TX2_Horner0_6.after 1#usize=
        ok (.Ok JGo_TX2_Horner1_6.after) := by
  classical
  have h := RowFinish_Control.round_value (FIo_Install.finishOps (.Ok ()) seed)
    (JFw_Frames.window 7783 224) JFq_Alpha1.scalar JGo_TX2_Horner0_6.after 1#usize
    (JGo_TX2_Round1.values seed)
  change _=ok (if JGo_TX2_Round1.boundary=JGo_TX2_Round1.boundary
    then core.result.Result.Ok JGo_TX2_Horner1_6.after else core.result.Result.Err AspisR1Stage2.verifier.Error.Relation) at h
  rw [if_pos rfl] at h
  exact h
#print axioms second
end AspisR1.JGo_TX2_RoundCalls
end
